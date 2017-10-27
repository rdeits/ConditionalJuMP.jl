module cj3

using JuMP
using JuMP: GenericAffExpr, GenericRangeConstraint, Variable, AbstractJuMPScalar
using IntervalArithmetic: Interval
import Base: hash, ==, show, &, !


function simplify(e::JuMP.GenericAffExpr{T, Variable}) where T
    coeffs = Dict{Variable, T}()
    for i in eachindex(e.vars)
        v, c = e.vars[i], e.coeffs[i]
        if c != 0
            coeffs[v] = get(coeffs, v, zero(T)) + c
        end
    end
    pairs = collect(coeffs)
    sort!(pairs)
    constant = e.constant
    if iszero(constant)
        constant = zero(constant)
    end
    AffExpr(first.(pairs), last.(pairs), constant)
end



function normalize(c::GenericRangeConstraint)
    @assert c.ub != Inf || c.lb != -Inf "Can't construct a constraint with infinite lower and upper bounds"

    terms = c.terms
    lb = c.lb
    ub = c.ub
    if ub == Inf
        # then flip the constraint over so its upper bound is finite
        lb, ub = -ub, -lb
        terms = -terms
    end
    if ub != 0
        x = ub
        ub = 0
        terms -= x
        lb -= x
    end
    if iszero(lb)
        # Ensure that we don't have negative zeros so that hashing is reliable
        lb = zero(lb)
    end
    if iszero(ub)
        ub = zero(ub)
    end
    GenericRangeConstraint(simplify(terms), lb, ub)
end


struct Constraint{T}
    c::GenericRangeConstraint{GenericAffExpr{T, Variable}}
    function Constraint{T}(c::GenericAffExpr{T}, lb, ub) where T
        new(normalize(GenericRangeConstraint{GenericAffExpr{T, Variable}}(c, lb, ub)))
    end
end

function Constraint(c::GenericAffExpr{T1}, lb::T2, ub::T3) where {T1, T2, T3}
    Constraint{promote_type(T1, T2, T3)}(c, lb, ub)
end

# work-around because JuMP doesn't properly define hash()
function Base.hash(x::Constraint, h::UInt)
    h = hash(x.c.lb, h)
    h = hash(x.c.ub, h)
    h = hash(x.c.terms.constant, h)
    for v in x.c.terms.vars
        h = hash(v, h)
    end
    for c in x.c.terms.coeffs
        h = hash(c, h)
    end
    h
end

(==)(e1::Constraint, e2::Constraint) = (e1.c.lb == e2.c.lb) && (e1.c.ub == e2.c.ub) && (e1.c.terms == e2.c.terms)

# struct Conditional
#     constraints::Set{Constraint{Float64}}
# end

const Conditional = Set{Constraint{Float64}}

Conditional(::typeof(<=), x, y) = Conditional(Set([Constraint(x - y, -Inf, 0)]))
Conditional(::typeof(>=), x, y) = Conditional(Set([Constraint(y - x, -Inf, 0)]))
Conditional(::typeof(==), x, y) = Conditional(Set([Constraint(x - y, 0, 0)]))
(&)(c1::Conditional, c2::Conditional) = union(c1, c2)

nan_to_null(x) = isnan(x) ? Nullable{typeof(x)}() : Nullable{typeof(x)}(x)

"""
Like JuMP.getvalue, but returns a Nullable{T}() for unset variables instead
of throwing a warning
"""
_getvalue(x::Variable) = nan_to_null(JuMP._getValue(x))
_getvalue(x::Number) = nan_to_null(x)

function _getvalue(x::JuMP.GenericAffExpr{T, Variable}) where {T}
    result::Nullable{T} = x.constant
    for i in eachindex(x.coeffs)
        result = result .+ x.coeffs[i] .* _getvalue(x.vars[i])
    end
    result
end

function _getvalue(h::Constraint)
    v = _getvalue(h.c.terms)
    max.(v .- h.c.ub, h.c.lb .- v)
end

_getvalue(c::Conditional) = maximum(_getvalue, c)

struct UnhandledComplementException <: Exception
    c::Conditional
end

function Base.showerror(io::IO, e::UnhandledComplementException)
    print(io, "The complement of condition $(e.c) cannot be automatically determined. You will need to manually specify a disjunction covering this condition and all of its alternatives")
end

# lb <= x <= ub
# -> x <= lb || x >= ub
hascomplement(c::Conditional) = (length(c) == 1) && (first(c).c.lb == -Inf || first(c).c.ub == Inf)
function complement(c::Conditional)
    hascomplement(c) || throw(UnhandledComplementException(c))
    constr = first(c).c
    if constr.lb == -Inf
        new_constr = Constraint(constr.terms, constr.ub, Inf)
    else
        @assert constr.ub == Inf
        new_constr = Constraint(constr.terms, -Inf, constr.lb)
    end
    Conditional([new_constr])
end
(!)(c::Conditional) = complement(c)

lowerbound(x::Number) = x
upperbound(x::Number) = x
lowerbound(x::Variable) = JuMP.getlowerbound(x)
upperbound(x::Variable) = JuMP.getupperbound(x)

function interval(e::JuMP.GenericAffExpr{T, Variable}) where {T}
    if isempty(e.coeffs)
        return Interval(e.constant, e.constant)
    else
        result = Interval(e.constant, e.constant)
        for i in eachindex(e.coeffs)
            var = e.vars[i]
            coef = e.coeffs[i]
            result += Interval(coef, coef) * Interval(getlowerbound(var), getupperbound(var))
        end
        return result
    end
end

upperbound(e::GenericAffExpr) = upperbound(interval(e))
lowerbound(e::GenericAffExpr) = lowerbound(interval(e))
lowerbound(i::Interval) = i.lo
upperbound(i::Interval) = i.hi

const Implication = Pair{Conditional, Conditional}

struct IndicatorMap
    model::Model
    indicators::Dict{Conditional, AffExpr}
    disjunctions::Vector{Vector{Implication}}
    y_idx::Base.RefValue{Int}
    z_idx::Base.RefValue{Int}
end

IndicatorMap(m::Model) = IndicatorMap(m, 
    Dict{Conditional, AffExpr}(), 
    Vector{Vector{Implication}}(),
    Ref(1),
    Ref(1))

getindmap!(m::Model) = get!(m.ext, :indicator_map, IndicatorMap(m))::IndicatorMap

function newcontinuousvar(m::IndicatorMap)
    var = @variable(m.model, basename="y_{anon$(m.y_idx[])}")
    m.y_idx[] = m.y_idx[] + 1
    var
end

function newcontinuousvar(m::IndicatorMap, size::Dims)
    var = reshape(@variable(m.model, [1:prod(size)], basename="{y_{anon$(m.y_idx[])}}"), size)
    m.y_idx[] = m.y_idx[] + 1
    var
end

newcontinuousvar(m::Model, args...) = newcontinuousvar(getindmap!(m), args...)

function newbinaryvar(m::IndicatorMap)
    var = @variable(m.model, basename="z_{anon$(m.z_idx[])}", category=:Bin)
    m.z_idx[] = m.z_idx[] + 1
    var
end

newbinaryvar(m::Model, args...) = newbinaryvar(getindmap!(m), args...)

function getindicator!(m::IndicatorMap, c::Conditional, can_create=true)
    if haskey(m.indicators, c)
        return m.indicators[c]
    else
        if !can_create
            @show c
            error("Not allowed to create a new variable here. Something has gone wrong")
        end
        z = convert(AffExpr, newbinaryvar(m))
        implies!(m.model, z, c)
        m.indicators[c] = z

        if hascomplement(c)
            m.indicators[!c] = 1 - z
        end
        return z
    end
end

getindicator!(m::Model, c::Conditional) = getindicator!(getindmap!(m), c)

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional)
    for constraint in c
        implies!(m, z, constraint)
    end
end

struct UnboundedVariableException <: Exception
    terms::AffExpr
end

function Base.showerror(io::IO, e::UnboundedVariableException)
    print(io, "Cannot create an implication involving the expression: $(e.terms) because not all of the variables in it are fully bounded. Please use `JuMP.setlowerbound()` and `JuMP.setupperbound()` to set finite bounds for all variables appearing in this expression.")
end

function implies!(m::Model, z::AbstractJuMPScalar, constraint::Constraint)
    expr_interval = interval(constraint.c.terms)
    if constraint.c.ub != Inf
        M = upperbound(expr_interval) - constraint.c.ub
        isfinite(M) || throw(UnboundedVariableException(constraint.c.terms))
        @constraint m constraint.c.terms <= constraint.c.ub + M * (1 - z)
    end
    if constraint.c.lb != -Inf
        M = constraint.c.lb - lowerbound(expr_interval)
        isfinite(M) || throw(UnboundedVariableException(constraint.c.terms))
        @constraint m constraint.c.terms >= constraint.c.lb - M * (1 - z)
    end
end

disjunction!(m::Model, args...) = disjunction!(getindmap!(m), args...)

function disjunction!(indmap::IndicatorMap, imps::NTuple{1, Implication})
    z = newbinaryvar(indmap)
    JuMP.fix(z, 1)
    lhs, rhs = imps[1]
    implies!(indmap.model, z, lhs)
    implies!(indmap.model, z, rhs)
    implies!(indmap.model, 1 - z, !lhs)
end

function disjunction!(indmap::IndicatorMap, imps::NTuple{2, Implication})
    z = getindicator!(indmap, first(imps[1]))
    implies!(indmap.model, z, last(imps[1]))
    indmap.indicators[first(imps[2])] = 1 - z
    implies!(indmap.model, 1 - z, first(imps[2]))
    implies!(indmap.model, 1 - z, last(imps[2]))
    push!(indmap.disjunctions, collect(imps))
end

function  disjunction!(indmap::IndicatorMap, 
                       conditions::Union{Tuple{Vararg{<:Conditional}},
                                         <:AbstractArray{<:Conditional}})
    disjunction!(indmap, (c -> (c => Conditional(Set()))).(conditions))
end

implies!(m::Model, imps::Implication...) = disjunction!(m, imps)

function implies!(m::Model, imp::Implication)
    c1, c2 = imp
    comp1 = !c1
    disjunction!(m, (imp, (comp1 => Conditional(Set()))))
end


# show(io::IO, h::HashableAffExpr) = print(io, h.expr)

# function show(io::IO, c::Conditional)
#     print(io, join(["($arg <= 0)" for arg in c.args], " & "))
# end

end
    