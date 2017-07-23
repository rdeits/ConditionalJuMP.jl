module ConditionalJuMP

using JuMP
using JuMP: AbstractJuMPScalar
using MacroTools: @capture
using IntervalArithmetic: Interval, mid, radius
import Base: <=, ==, >=, !

export @disjunction,
    @implies,
    @conditional,
    implies!,
    disjunction!,
    setup_indicators!,
    upperbound,
    lowerbound

const JExpr = JuMP.GenericAffExpr{Float64, Variable}

getmodel(x::JuMP.Variable) = x.m
getmodel(x::JuMP.GenericAffExpr) = x.vars[1].m
getmodel(x) = nothing

nan_to_null(x) = isnan(x) ? Nullable{typeof(x)}() : Nullable{typeof(x)}(x)
null_to_nan(x::Nullable) = isnull(x) ? NaN : get(x)

"""
Like JuMP.getvalue, but never throws warnings for unset variables
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

_setvalue(v::Variable, x::Nullable) = JuMP.setvalue(v, null_to_nan(x))
_setvalue(v::Variable, x) = JuMP.setvalue(v, x)

struct Conditional{Op, N, Args<:Tuple{Vararg{<:Any, N}}}
    op::Op
    args::Args

    function Conditional{Op, N, Args}(op::Op, args::Args) where {Op, N, Args}
        canonical_op, canonical_args = canonicalize(op, args)
        new{typeof(canonical_op), N, typeof(canonical_args)}(canonical_op, canonical_args)
    end
end

Conditional(op::Op, args::Vararg{<:Any, N}) where {Op, N} = Conditional{Op, N, typeof(args)}(op, args)

function getmodel(c::Conditional)
    for arg in c.args
        if getmodel(arg) != nothing
            return getmodel(arg)
        end
    end
    error("Could not find JuMP Model in conditional $c")
end

Conditional(::typeof(>=), x, y) = Conditional(<=, -x, -y)

function _getvalue(c::Conditional)
    c.op.(_getvalue.(c.args)...)
end

Base.show(io::IO, c::Conditional) = print(io, c.op, c.args)

canonicalize(op, args) = op, args
canonicalize(op::typeof(>=), args::Tuple{Vararg{<:Any, 2}}) = (<=, (args[2] - args[1], 0))
canonicalize(op::typeof(<=), args::Tuple{Vararg{<:Any, 2}}) = (<=, (args[1] - args[2], 0))

(==)(c1::Conditional{op}, c2::Conditional{op}) where {op} = c1.args == c2.args

Base.hash(c::Conditional{typeof(>=)}, h::UInt) = hash(canonicalize(c), h)

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

function Base.hash(c::Union{<:Conditional{typeof(<=), 2}, <:Conditional{typeof(==), 2}}, h::UInt)
    h = hash(c.op, h)
    _hash(c.args[1] - c.args[2], h)
end

struct Implication{C1 <: Conditional, C2 <: Conditional}
    lhs::C1
    rhs::C2
end

Base.show(io::IO, cv::Implication) = print(io, cv.rhs, " if ", cv.lhs)

struct ComplementNotDefined
end

complement(c::Conditional) = ComplementNotDefined()
complement(c::Conditional{typeof(<=), 2}) = Conditional(<=, c.args[2], c.args[1])
complement(c::Conditional{typeof(>=), 2}) = Conditional(<=, c.args[1], c.args[2])
(!)(c::Conditional) = complement(c)

macro implies(m, lhs, rhs)
    quote
        c1 = $(_conditional(lhs))
        c2 = $(_conditional(rhs))
        @assert !isa(!c1, ComplementNotDefined)
        implies!($(esc(m)), c1, c2)
    end
end


function _conditional(ex::Expr)
    if @capture(ex, op_(lhs_, rhs_))
        quote
            Conditional($(esc(op)), $(esc(lhs)), $(esc(rhs)))
        end
    else
        error("Could not parse: $ex. Expected `@conditional(x <= y)`")
    end
end

macro conditional(ex)
    _conditional(ex)
end

lowerbound(x::Number) = x
lowerbound(x::AbstractJuMPScalar) = -upperbound(-x)
upperbound(x::Number) = x
upperbound(x::Variable) = JuMP.getupperbound(x)

function upperbound(e::JuMP.GenericAffExpr{T, Variable}) where {T}
    intervals = [Interval(getlowerbound(v), getupperbound(v)) for v in e.vars]
    if isempty(intervals)
        ex_bounds = Interval(e.constant, e.constant)
    else
        ex_bounds = e.coeffs' * intervals + e.constant
    end
    mid(ex_bounds) + radius(ex_bounds)
end

require!(m::Model, c::Conditional{typeof(<=), 2}) = @constraint(m, c.args[1] <= c.args[2])
function require!(m::Model, c::Conditional{typeof(==), 2})
    lhs, rhs = c.args
    constraint = @constraint(m, lhs == rhs)
    _setvalue(lhs, rhs)
    constraint
end
require!(m::Model, ::ComplementNotDefined) = nothing

function implies!(m::Model, c1::Conditional, c2::Conditional)
    push!(get!(m.ext, :implications, Implication[]), Implication(c1, c2))
end

function Base.ifelse(c::Conditional, v1, v2)
    @assert size(v1) == size(v2)
    m = getmodel(c)
    y = @variable(m, y, basename="y")
    setlowerbound.(y, min.(lowerbound.(v1), lowerbound.(v2)))
    setupperbound.(y, max.(upperbound.(v1), upperbound.(v2)))
    implies!(m, c, @conditional y == v1)
    implies!(m, !c, @conditional y == v2)
    y
end

function Base.ifelse(c::Conditional, v1::AbstractArray, v2::AbstractArray)
    @assert size(v1) == size(v2)
    m = getmodel(c)
    y = reshape(@variable(m, y[1:length(v1)], basename="y"), size(v1))
    setlowerbound.(y, min.(lowerbound.(v1), lowerbound.(v2)))
    setupperbound.(y, max.(upperbound.(v1), upperbound.(v2)))
    implies!(m, c, @conditional y == v1)
    implies!(m, !c, @conditional y == v2)
    y
end

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional{typeof(<=), 2})
    lhs, rhs = c.args
    g = lhs .- rhs
    M = upperbound.(g)
    @assert all(isfinite(M))
    if isa(g, AbstractArray)
        @constraint m lhs .<= rhs .+ M .* (1 .- z)
    else
        @constraint m lhs <= rhs + M * (1 - z)
    end
end 

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional{typeof(==), 2})
    lhs, rhs = c.args
    g = lhs .- rhs
    M_u = upperbound.(g)
    @assert all(isfinite, M_u)
    M_l = lowerbound.(g)
    @assert all(isfinite, M_l)
    if isa(g, AbstractArray)
        @constraint(m, lhs .- rhs .<= M_u .* (1 .- z))
        @constraint(m, lhs .- rhs .>= M_l .* (1 .- z))
    else
        @constraint(m, lhs - rhs <= M_u * (1 - z))
        @constraint(m, lhs - rhs >= M_l * (1 - z))
    end
end 

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional{typeof(all)})
    for arg in c.args
        implies!(m, z, arg)
    end
end

struct Disjunction{T <: Tuple{Vararg{<:Conditional}}}
    cases::T
end

function disjunction!(m::Model, cs::Conditional...)
    push!(get!(m.ext, :disjunctions, Disjunction[]), Disjunction(cs))
end

struct IndicatorMap
    model::Model
    indicators::Dict{Conditional, Variable}
    idx::Base.RefValue{Int}
end

IndicatorMap(m::Model) = IndicatorMap(m, Dict{Conditional, Variable}(), Ref(1))

struct UnhandledComplementException <: Exception
    c::Conditional
end

function Base.showerror(io::IO, e::UnhandledComplementException)
    print(io, "The complement of condition $(e.c) cannot be automatically determined. You will need to manually specify a disjunction covering this condition and all of its alternatives")
end

function getindicator!(m::IndicatorMap, c::Conditional)
    if haskey(m.indicators, c)
        return m.indicators[c]
    elseif haskey(m.indicators, !c)
        return 1 - m.indicators[!c]
    else
        z = @variable(m.model, category=:Bin, basename="z_$(m.idx[])")
        implies!(m.model, z, c)
        m.idx[] = m.idx[] + 1
        compl = !c
        if isa(compl, ComplementNotDefined)
            found = any(c in dis.cases for dis in get(m.model.ext, :disjunctions, Disjunction[]))
            if !found
                throw(UnhandledComplementException(c))
            end
        else
            implies!(m.model, 1 - z, compl)
        end
        m.indicators[c] = z
        return z
    end
end

function _setup_indicator!(m::Model, imp::Implication, indicators::IndicatorMap)
    z = getindicator!(indicators, imp.lhs)
    implies!(m, z, imp.rhs)
    nothing
end

function _setup_implication!(m::Model, imp::Implication, indicators::IndicatorMap)
    sat = _getvalue(imp.lhs)
    if isnull(sat)
        _setup_indicator!(m, imp, indicators)
    elseif get(sat)
        require!(m, imp.lhs)
        require!(m, imp.rhs)
    else
        require!(m, !(imp.lhs))
    end
end

function _setup_disjunction!(m::Model, d::Disjunction, indicators::IndicatorMap)
    if all(isnull, _getvalue.(d.cases))
        zs = getindicator!.(indicators, d.cases)
        @constraint(m, sum(zs) == 1)
    end
end

function _setup_indicators!(m::Model)
    indicators = IndicatorMap(m)
    for x in get!(m.ext, :implications, Implication[])
        _setup_implication!(m, x, indicators)
    end
    empty!(m.ext[:implications])
    for x in get!(m.ext, :disjunctions, Disjunction[])
        _setup_disjunction!(m, x, indicators)
    end
    empty!(m.ext[:disjunctions])
end

function setup_indicators!(m::Model)
    prev = copy(m.colVal)
    m.colVal .= NaN
    _setup_indicators!(m)
    m.colVal[1:length(prev)] .= prev
    m
end

function with_assignment!(f::Function, m::Model, assignment::Pair{Variable, <:Number})
    prev = _getvalue(assignment.first)
    _setvalue(assignment.first, assignment.second)
    f()
    _setvalue(assignment.first, prev)
end

function with_assignment!(f::Function, m::Model, assignment::Pair{<:AbstractArray{Variable}, <:AbstractArray{<:Number}})
    prev = _getvalue.(assignment.first)
    _setvalue.(assignment.first, assignment.second)
    f()
    _setvalue.(assignment.first, prev)
end

function setup_indicators!(m::Model, assignment, assignments...)
    with_assignment!(m, assignment) do
        _setup_indicators!(m, assignments...)
    end
    m
end

macro disjunction(ex)
    if @capture(ex, if c1_; v1_; else v2_; end)
        cond_expr = _conditional(c1)
    else
        error("Could not parse: $ex")
    end
    quote
        if isa($(cond_expr).args[1] - $(cond_expr).args[2], AbstractJuMPScalar)
            ifelse($(cond_expr), $(esc(v1)), $(esc(v2)))
        else
            $(esc(ex))
        end
    end
end
            

end