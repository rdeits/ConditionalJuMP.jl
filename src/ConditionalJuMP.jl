__precompile__()

module ConditionalJuMP

using JuMP
using JuMP: AbstractJuMPScalar
using IntervalArithmetic: Interval
import Base: <=, ==, >=, !, &

export @disjunction,
    @implies,
    @?,
    @switch,
    @ifelse,
    warmstart!,
    upperbound,
    lowerbound

include("macros.jl")

getmodel(x::JuMP.Variable) = x.m
getmodel(x::JuMP.GenericAffExpr) = x.vars[1].m
getmodel(x) = nothing

nan_to_null(x) = isnan(x) ? Nullable{typeof(x)}() : Nullable{typeof(x)}(x)

"""
Like JuMP.getvalue, but returns a Nullable{T}() for unset variables instead
of throwing a warning
"""
function _getvalue(x::JuMP.GenericAffExpr{T, Variable}) where {T}
    result::Nullable{T} = x.constant
    for i in eachindex(x.coeffs)
        result = result .+ x.coeffs[i] .* _getvalue(x.vars[i])
    end
    result
end

_getvalue(x::Variable) = nan_to_null(JuMP._getValue(x))
_getvalue(x::Number) = nan_to_null(x)

_setvalue(v::Variable, x) = JuMP.setvalue(v, x)
function _setvalue(s::JuMP.GenericAffExpr, x)
    @assert length(s.vars) == 1
    _setvalue(s.vars[1], (x - s.constant) / s.coeffs[1])
end

struct Conditional{Op, Args <: Tuple}
    op::Op
    args::Args

    function Conditional(op, args) where {}
        canonical_op, canonical_args = canonicalize(op, args)
        new{typeof(canonical_op), typeof(canonical_args)}(
            canonical_op, canonical_args)
    end
end

function getmodel(c::Conditional)
    for arg in c.args
        if getmodel(arg) != nothing
            return getmodel(arg)
        end
    end
    error("Could not find JuMP Model in conditional $c")
end

Conditional(::typeof(>=), x, y) = Conditional(<=, (-x, -y))
(&)(c1::Conditional, cs::Conditional...) = Conditional(&, (c1, cs...))

Narg{N} = Tuple{Vararg{Any, N}}

_getvalue(c::Conditional{typeof(<=), <:Narg{2}}) = _getvalue(c.args[1]) .- _getvalue(c.args[2])
_getvalue(c::Conditional{typeof(>=), <:Narg{2}}) = _getvalue(c.args[2]) .- _getvalue(c.args[1])
_getvalue(c::Conditional{typeof(==), <:Narg{2}}) = abs.(_getvalue(c.args[1]) .- _getvalue(c.args[2]))
_getvalue(c::Conditional{typeof(&)}) = maximum(x -> _getvalue.(x), c.args)

Base.show(io::IO, c::Conditional) = print(io, c.op, c.args)

canonicalize(op, args) = op, args
canonicalize(op::typeof(>=), args::Tuple{Vararg{<:Any, 2}}) = (<=, (args[2] - args[1], 0))
canonicalize(op::typeof(<=), args::Tuple{Vararg{<:Any, 2}}) = (<=, (args[1] - args[2], 0))
# canonicalize(c::Conditional) = canonicalize(c.op, c.args)

(==)(c1::Conditional{op}, c2::Conditional{op}) where {op} = c1.args == c2.args

# Base.hash(c::Conditional{typeof(>=)}, h::UInt) = hash(canonicalize(c), h)

# work-around because JuMP doesn't properly define hash()
function _hash(x::JuMP.GenericAffExpr, h::UInt)
    h = hash(x.constant, h)
    for v in x.vars
        h = hash(v, h)
    end
    for c in x.coeffs
        h = hash(c, h)
    end
    h
end

function Base.hash(c::Union{<:Conditional{typeof(<=), <:Narg{2}}, <:Conditional{typeof(==), <:Narg{2}}}, h::UInt)
    h = hash(c.op, h)
    _hash(c.args[1] - c.args[2], h)
end

const Implication{C1, C2} = Pair{C1, C2} where {C1 <: Conditional, C2 <: Union{Conditional, Void}}

second(x::Pair) = x.second

Base.show(io::IO, cv::Implication) = print(io, "(", first(cv), ") implies (", second(cv), ")")

struct ComplementNotDefined
end

complement(c::Conditional) = ComplementNotDefined()
complement(c::Conditional{typeof(<=), <:Narg{2}}) = Conditional(<=, (c.args[2], c.args[1]))
complement(c::Conditional{typeof(>=), <:Narg{2}}) = Conditional(<=, (c.args[1], c.args[2]))
(!)(c::Conditional) = complement(c)

Base.@pure isjump(x) = false
Base.@pure isjump(args::Tuple) = any(isjump, args)
Base.@pure isjump(arg::Pair) = isjump(arg.first)
Base.@pure isjump(c::Conditional) = isjump(c.args[1])
Base.@pure isjump(x::AbstractJuMPScalar) = true
Base.@pure isjump(x::AbstractArray{<:AbstractJuMPScalar}) = true

function _conditional(op::Op, args...) where {Op <: Union{typeof(<=), typeof(>=), typeof(==), typeof(in)}}
    if isjump(args)
        Conditional(op, args)
    else
        op(args...)
    end
end

_conditional(op, args...) = op(args...)

function _all_conditional(args)
    (&)(args...)
end

lowerbound(x::Number) = x
upperbound(x::Number) = x
lowerbound(x::Variable) = JuMP.getlowerbound(x)
upperbound(x::Variable) = JuMP.getupperbound(x)
lowerbound(x::AbstractJuMPScalar) = -upperbound(-x)

function simplify(e::JuMP.GenericAffExpr{T, Variable}) where T
    coeffs = Dict{Variable, T}()
    for i in eachindex(e.vars)
        v, c = e.vars[i], e.coeffs[i]
        if c != 0
            coeffs[v] = get(coeffs, v, zero(T)) + c
        end
    end
    coeffs
end

function upperbound(e::JuMP.GenericAffExpr{T, Variable}) where {T}
    coeffs = simplify(e)
    if isempty(coeffs)
        return e.constant
    else
        result = Interval(e.constant, e.constant)
        for (var, coef) in coeffs
            result += Interval(coef, coef) * Interval(getlowerbound(var), getupperbound(var))
        end
        return result.hi
    end
end

struct IndicatorMap
    model::Model
    indicators::Dict{Conditional, AbstractJuMPScalar}
    disjunctions::Vector{Vector{Implication}}
    y_idx::Base.RefValue{Int}
    z_idx::Base.RefValue{Int}
end

IndicatorMap(m::Model) = IndicatorMap(m, 
    Dict{Conditional, Variable}(), 
    Vector{Vector{Implication}}(),
    Ref(1),
    Ref(1))

struct UnhandledComplementException <: Exception
    c::Conditional
end

function Base.showerror(io::IO, e::UnhandledComplementException)
    print(io, "The complement of condition $(e.c) cannot be automatically determined. You will need to manually specify a disjunction covering this condition and all of its alternatives")
end

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
        z = newbinaryvar(m)
        implies!(m.model, z, c)
        m.indicators[c] = z

        compl = !c
        if !isa(compl, ComplementNotDefined)
            m.indicators[compl] = 1 - z
        end
        return z
    end
end


getindicator!(m::Model, c::Conditional) = getindicator!(getindmap!(m), c)

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
    implies!(indmap.model, z, second(imps[1]))
    indmap.indicators[first(imps[2])] = 1 - z
    implies!(indmap.model, 1 - z, first(imps[2]))
    implies!(indmap.model, 1 - z, second(imps[2]))
    push!(indmap.disjunctions, Implication[imps...])
end

function disjunction!(indmap::IndicatorMap, imps::Union{Tuple, AbstractArray})
    zs = getindicator!.(indmap, first.(imps))
    implies!.(indmap.model, zs, second.(imps))
    @constraint(indmap.model, sum(zs) == 1)
    push!(indmap.disjunctions, Implication[imps...])
end

function  disjunction!(indmap::IndicatorMap, 
                       conditions::Union{Tuple{Vararg{<:Conditional}},
                                         <:AbstractArray{<:Conditional}})
    disjunction!(indmap, (c -> (c => nothing)).(conditions))
end

disjunction!(m::Model, args...) = disjunction!(getindmap!(m), args...)

implies!(m::Model, imp::Implication...) = disjunction!(m, imp)

function implies!(m::Model, imp::Implication)
    c1, c2 = imp
    comp1 = !c1
    if isa(comp1, ComplementNotDefined)
        throw(UnhandledComplementException(c1))
    end
    disjunction!(m, (imp, (comp1 => nothing)))
end

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional{typeof(<=), <:Narg{2}})
    lhs, rhs = c.args
    g = lhs - rhs
    M = upperbound(g)
    if !all(isfinite(M))
        error("Cannot create an implication for an unbounded variable. Please use `JuMP.setlowerbound()` and `JuMP.setupperbound()` to set finite bounds for all variables appearing in this expression.")
    end
    @constraint m lhs <= rhs + M * (1 - z)
end 

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional{typeof(==), <:Narg{2}})
    lhs, rhs = c.args
    g = lhs - rhs
    M_u = upperbound(g)
    M_l = lowerbound(g)
    if !all(isfinite(M_u)) || !all(isfinite(M_l))
        error("Cannot create an implication for an unbounded variable. Please use `JuMP.setlowerbound()` and `JuMP.setupperbound()` to set finite bounds for all variables appearing in this expression.")
    end
    @constraint(m, lhs - rhs <= M_u * (1 - z))
    @constraint(m, lhs - rhs >= M_l * (1 - z))
end 

implies!(::Model, ::AbstractJuMPScalar, ::Void) = nothing
implies!(::Model, ::AbstractJuMPScalar, ::ComplementNotDefined) = nothing

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional{typeof(&)})
    for arg in c.args
        implies!(m, z, arg)
    end
end

function switch!(m::Model, args::Pair{<:Conditional}...)
    y = newcontinuousvar(m)
    conditions = first.(args)
    values = second.(args)
    setlowerbound(y, minimum(lowerbound, values))
    setupperbound(y, maximum(upperbound, values))
    disjunction!(m, map(cv -> (cv[1] => @?(y == cv[2])), args))
    y
end

function switch!(m::Model, args::Pair{<:Conditional, <:AbstractArray}...)
    y = newcontinuousvar(m, size(args[1].second))
    conditions = first.(args)
    values = second.(args)
    for I in eachindex(y)
        setlowerbound(y[I], minimum(v -> lowerbound(v[I]), values))
        setupperbound(y[I], maximum(v -> upperbound(v[I]), values))
    end
    disjunction!(m, map(cv -> (cv[1] => @?(y .== cv[2])), args))
    y
end


function Base.ifelse(c::Conditional, v1, v2)
    @assert size(v1) == size(v2)
    m = getmodel(c)
    y = newcontinuousvar(m)
    setlowerbound.(y, min.(lowerbound.(v1), lowerbound.(v2)))
    setupperbound.(y, max.(upperbound.(v1), upperbound.(v2)))
    disjunction!(m, (c => @?(y == v1), !c => @?(y == v2)))
    y
end

function Base.ifelse(c::Conditional, v1::AbstractArray, v2::AbstractArray)
    @assert size(v1) == size(v2)
    m = getmodel(c)
    y = newcontinuousvar(m, size(v1))
    setlowerbound.(y, min.(lowerbound.(v1), lowerbound.(v2)))
    setupperbound.(y, max.(upperbound.(v1), upperbound.(v2)))
    @disjunction(m, (c => y .== v1), (!c => (y .== v2)))
    # disjunction!(m, (c => @?(y .== v1), !c => @?(y .== v2)))
    y
end

isfixed(v::Variable) = JuMP.getcategory(v) == :Fixed
isfixed(s::JuMP.GenericAffExpr) = all(isfixed, s.vars)

_fix(v::Variable, x) = JuMP.fix(v, x)

function _fix(s::JuMP.GenericAffExpr, x)
    @assert length(s.vars) == 1
    @assert s.coeffs[1] != 0
    JuMP.fix(s.vars[1], (x - s.constant) / s.coeffs[1])
    @assert get(_getvalue(s)) ≈ x
end

_unfix(v::Variable) = JuMP.setcategory(v, :Bin)

function _unfix(s::JuMP.GenericAffExpr)
    @assert length(s.vars) == 1
    JuMP.setcategory(s.vars[1], :Bin)
    setlowerbound(s.vars[1], 0)
    setupperbound(s.vars[1], 1)
end

function _setvalue(m::Model, c::Conditional{typeof(==), <:Narg{2}})
    _setvalue(c.args[1] - c.args[2], 0)
    nothing
end

# Fallback methods for most conditionals
_setvalue(m::Model, c::Conditional) = nothing
_setvalue(m::Model, ::Void) = nothing

function warmstart!(m::Model, fix=false)
    indmap = getindmap!(m)
    while true
        modified = false
        for implications in indmap.disjunctions
            violations = Nullable{Float64}[_getvalue(first(i)) for i in implications]
            if !any(isnull, violations)
                best_match = indmin(get.(violations))
                for i in eachindex(violations)
                    imp = implications[i]
                    lhs, rhs = imp
                    z = getindicator!(indmap, lhs, false)
                    satisfied = i == best_match
                    if fix
                        if !isfixed(z)
                            modified = true
                        end
                        _fix(z, satisfied)
                    else
                        if isnull(_getvalue(z))
                            modified = true
                        end
                        _unfix(z)
                        _setvalue(z, satisfied)
                    end
                    if satisfied
                        _setvalue(m, rhs)
                    end
                end
            end
        end
        if !modified
            break
        end
    end
end

function switch(args::Pair...)
    if isjump(args)
        switch!(getmodel(args[1].first), args...)
    else
        for arg in args
            if arg.first
                return arg.second
            end
        end
        error("One of the cases in the switch statement must always match")
    end
end

end