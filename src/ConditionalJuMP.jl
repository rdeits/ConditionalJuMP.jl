__precompile__()

module ConditionalJuMP

using JuMP
using JuMP: AbstractJuMPScalar
using MacroTools: @capture
using IntervalArithmetic: Interval, mid, radius
import Base: <=, ==, >=, !, &

export @disjunction,
    @implies,
    @?,
    @switch,
    setup_indicators!,
    upperbound,
    lowerbound

include("macros.jl")

const JExpr = JuMP.GenericAffExpr{Float64, Variable}

getmodel(x::JuMP.Variable) = x.m
getmodel(x::JuMP.GenericAffExpr) = x.vars[1].m
getmodel(x) = nothing

nan_to_null(x) = isnan(x) ? Nullable{typeof(x)}() : Nullable{typeof(x)}(x)
null_to_nan(x::Nullable) = isnull(x) ? NaN : get(x)

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

_setvalue(v::Variable, x::Nullable) = JuMP.setvalue(v, null_to_nan(x))
_setvalue(v::Variable, x) = JuMP.setvalue(v, x)
function _setvalue(s::JuMP.GenericAffExpr, x)
    @assert length(s.vars) == 1
    _setvalue(s.vars[1], (x - s.constant) / s.coeffs[1])
end

struct Conditional{Op, N, Args<:Tuple{Vararg{<:Any, N}}}
    op::Op
    args::Args
end

function Conditional(op::Op, args::Vararg{<:Any, N}) where {Op, N}
    canonical_op, canonical_args = canonicalize(op, args)
    Conditional{typeof(canonical_op), N, typeof(canonical_args)}(
        canonical_op, canonical_args)
end

function getmodel(c::Conditional)
    for arg in c.args
        if getmodel(arg) != nothing
            return getmodel(arg)
        end
    end
    error("Could not find JuMP Model in conditional $c")
end

Conditional(::typeof(>=), x, y) = Conditional(<=, -x, -y)
(&)(c1::Conditional, c2::Conditional) = Conditional(&, c1, c2)

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

const Implication{C1, C2} = Pair{C1, C2} where {C1 <: Conditional, C2 <: Union{Conditional, Void}}

second(x::Pair) = x.second

Base.show(io::IO, cv::Implication) = print(io, "(", first(cv), ") implies (", second(cv), ")")

struct ComplementNotDefined
end

complement(c::Conditional) = ComplementNotDefined()
complement(c::Conditional{typeof(<=), 2}) = Conditional(<=, c.args[2], c.args[1])
complement(c::Conditional{typeof(>=), 2}) = Conditional(<=, c.args[1], c.args[2])
(!)(c::Conditional) = complement(c)

Base.@pure isjump(x) = false
Base.@pure isjump(args::Tuple) = any(isjump, args)
Base.@pure isjump(arg::Pair) = isjump(arg.first)
Base.@pure isjump(c::Conditional) = isjump(c.args[1])
Base.@pure isjump(x::AbstractJuMPScalar) = true
Base.@pure isjump(x::AbstractArray{<:AbstractJuMPScalar}) = true

function _conditional(op::Op, args...) where {Op <: Union{typeof(<=), typeof(>=), typeof(==)}}
    if isjump(args)
        Conditional(op, args...)
    else
        op(args...)
    end
end

_conditional(op, args...) = op(args...)

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

struct IndicatorMap
    model::Model
    indicators::Dict{Conditional, AbstractJuMPScalar}
    implications::Dict{Conditional, Vector{Conditional}}
    idx::Base.RefValue{Int}
end

IndicatorMap(m::Model) = IndicatorMap(m, 
    Dict{Conditional, Variable}(), 
    Dict{Conditional, Vector{Conditional}}(),
    Ref(1))

struct UnhandledComplementException <: Exception
    c::Conditional
end

function Base.showerror(io::IO, e::UnhandledComplementException)
    print(io, "The complement of condition $(e.c) cannot be automatically determined. You will need to manually specify a disjunction covering this condition and all of its alternatives")
end

function getindicator!(m::IndicatorMap, c::Conditional)
    if haskey(m.indicators, c)
        return m.indicators[c]
    # elseif haskey(m.indicators, !c)
    #     return 1 - m.indicators[!c]
    else
        z = @variable(m.model, category=:Bin, basename="z_$(m.idx[])")
        implies!(m.model, z, c)
        m.idx[] = m.idx[] + 1
        m.indicators[c] = z

        compl = !c
        if !isa(compl, ComplementNotDefined)
            m.indicators[compl] = 1 - z
            implies!(m.model, 1 - z, compl)
        end
        return z
    end
end

getindmap!(m::Model) = get!(m.ext, :indicator_map, IndicatorMap(m))::IndicatorMap

getindicator!(m::Model, c::Conditional) = getindicator!(getindmap!(m), c)

function addimplication!(indmap::IndicatorMap, imp::Implication, addcomplement=true)
    c1, c2 = imp
    z = getindicator!(indmap, c1)
    if c2 !== nothing
        push!(get!(indmap.implications, c1, Conditional[]), c2)
    end
    implies!(indmap.model, z, c1)
    implies!(indmap.model, z, c2)
    if addcomplement
        implies!(indmap.model, 1 - z, !c1)
    end
    z
end

function addimplication!(indmap::IndicatorMap, imp::Implication...)
    zs = addimplication!.(indmap, imp, false)
    @constraint(indmap.model, sum(zs) == 1)
end

function addimplication!(indmap::IndicatorMap, imp::AbstractArray)
    zs = addimplication!.(indmap, imp, false)
    @constraint(indmap.model, sum(zs) == 1)
end

function implies!(m::Model, imp::Implication)
    c1, c2 = imp
    if isa(!c1, ComplementNotDefined)
        throw(UnhandledComplementException(c1))
    end
    addimplication!(m, imp)
end

function implies!(m::Model, i1::Implication, i2::Implication)
    indmap = getindmap!(m)
    z = addimplication!(indmap, i1)
    indmap.indicators[first(i2)] = 1 - z
    addimplication!(indmap, i2)
end

function implies!(m::Model, imps::Implication...)
    indmap = getindmap!(m)
    zs = addimplication!(indmap, imps...)
end


addimplication!(m::Model, args...) = addimplication!(getindmap!(m), args...)

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

implies!(::Model, ::AbstractJuMPScalar, ::Void) = nothing
implies!(::Model, ::AbstractJuMPScalar, ::ComplementNotDefined) = nothing

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional{typeof(&)})
    for arg in c.args
        implies!(m, z, arg)
    end
end

function switch!(m::Model, args::Pair{<:Conditional}...)
    y = @variable(m, y, basename="y")
    conditions = first.(args)
    values = second.(args)
    setlowerbound(y, minimum(lowerbound, values))
    setupperbound(y, maximum(upperbound, values))
    addimplication!(m, [c => @?(y == v) for (c, v) in args])
    y
end

function switch!(m::Model, args::Pair{<:Conditional, <:AbstractArray}...)
    y = reshape(@variable(m, y[1:length(args[1].second)], basename="y"), size(args[1].second))
    conditions = first.(args)
    values = second.(args)
    for I in eachindex(y)
        setlowerbound(y[I], minimum(v -> lowerbound(v[I]), values))
        setupperbound(y[I], maximum(v -> upperbound(v[I]), values))
    end
    addimplication!(m, [c => @?(y == v) for (c, v) in args])
    y
end


function Base.ifelse(c::Conditional, v1, v2)
    @assert size(v1) == size(v2)
    m = getmodel(c)
    y = @variable(m, y, basename="y")
    setlowerbound.(y, min.(lowerbound.(v1), lowerbound.(v2)))
    setupperbound.(y, max.(upperbound.(v1), upperbound.(v2)))
    addimplication!(m, c => @?(y == v1), !c => @?(y == v2))
    y
end

function Base.ifelse(c::Conditional, v1::AbstractArray, v2::AbstractArray)
    @assert size(v1) == size(v2)
    m = getmodel(c)
    y = reshape(@variable(m, y[1:length(v1)], basename="y"), size(v1))
    setlowerbound.(y, min.(lowerbound.(v1), lowerbound.(v2)))
    setupperbound.(y, max.(upperbound.(v1), upperbound.(v2)))
    addimplication!(m, c => @?(y == v1), !c => @?(y == v2))
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

function _setvalue(m::Model, c::Conditional{typeof(==), 2})
    _setvalue(c.args[1] - c.args[2], 0)
    nothing
end

_setvalue(m::Model, c::Conditional) = nothing

function setup_indicators!(m::Model, fix=false)
    indmap = getindmap!(m)
    while true
        modified = false
        for (condition, z) in indmap.indicators
            satisfied = _getvalue(condition)
            # @show condition satisfied
            if !isnull(satisfied)
                if fix
                    if !isfixed(z)
                        modified = true
                    end
                    _fix(z, get(satisfied))
                else
                    if isnull(_getvalue(z))
                        modified = true
                    end
                    _unfix(z)
                    _setvalue(z, get(satisfied))
                end
                if get(satisfied)
                    for c in get(indmap.implications, condition, [])
                        _setvalue(m, c)
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