module ConditionalJuMP

using JuMP
using JuMP: AbstractJuMPScalar
using MacroTools: @capture
using IntervalArithmetic: Interval, mid, radius
import Base: <=, ==, >=

export @disjunction,
    @implies,
    setup_indicators!,
    upperbound,
    lowerbound

getmodel(x::JuMP.Variable) = x.m
getmodel(x::JuMP.GenericAffExpr) = x.vars[1].m

"""
Like JuMP.getvalue, but never throws warnings for unset variables
"""
function _getvalue(x::JuMP.AffExpr)
    ret = x.constant
    for i in eachindex(x.vars)
        ret += x.coeffs[i] * _getvalue(x.vars[i])
    end
    ret
end

_getvalue(x::Variable) = JuMP._getValue(x)
_getvalue(x::Number) = x

struct Conditional{Op, T1, T2}
    op::Op
    lhs::T1
    rhs::T2
end

getmodel(c::Conditional) = getmodel(c.lhs - c.rhs)

Conditional(::typeof(>=), x, y) = Conditional(<=, -x, -y)

@enum TriState no yes maybe

function satisfied(c::Conditional)
    lhs = _getvalue(c.lhs)
    rhs = _getvalue(c.rhs)
    if isnan(lhs) || isnan(rhs)
        maybe
    elseif c.op(lhs, rhs)
        yes
    else
        no
    end
end

Base.show(io::IO, c::Conditional) = print(io, "(", c.lhs, " ", c.op, " ", c.rhs, ")")

complement(c::Conditional{typeof(<=)}) = Conditional(c.op, -c.lhs, -c.rhs)

struct Implication{C1 <: Conditional, C2 <: Conditional}
    lhs::C1
    rhs::C2
end

Base.show(io::IO, cv::Implication) = print(io, cv.rhs, " if ", cv.lhs)

struct Disjunction{T <: Implication}
    members::Vector{T}
end

Base.show(io::IO, d::Disjunction) = print(io, "(", join(d.members, " ⊻ "), ")")

macro implies(m, lhs, rhs)
    quote
        implies!($(esc(m)), 
            Implication(
                $(_conditional(lhs)),
                $(_conditional(rhs))))
    end
end


function _conditional(ex::Expr)
    if @capture(ex, op_(lhs_, rhs_))
        quote
            Conditional($(esc(op)), $(esc(lhs)), $(esc(rhs)))
        end
    else
        error("Could not parse: $ex. Expected `@conditional(x <= 0)`")
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

require!(m::Model, c::Conditional{typeof(<=)}) = @constraint(m, c.lhs <= c.rhs)
function require!(m::Model, c::Conditional{typeof(==)})
    constraint = @constraint(m, c.lhs == c.rhs)
    setvalue(c.lhs, c.rhs)
    constraint
end

function implies!(m::Model, imp::Implication)
    push!(get!(m.ext, :indicators, []), imp)
end

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional{typeof(<=)})
    g = c.lhs .- c.rhs
    M = upperbound.(g)
    @assert all(isfinite(M))
    if isa(g, AbstractArray)
        @constraint m c.lhs .<= c.rhs .+ M .* (1 .- z)
    else
        @constraint m c.lhs <= c.rhs + M * (1 - z)
    end
end 

function implies!(m::Model, z::AbstractJuMPScalar, c::Conditional{typeof(==)})
    g = c.lhs .- c.rhs
    M_u = upperbound.(g)
    @assert all(isfinite, M_u)
    M_l = lowerbound.(g)
    @assert all(isfinite, M_l)
    if isa(g, AbstractArray)
        @constraint(m, c.lhs .- c.rhs .<= M_u .* (1 .- z))
        @constraint(m, c.lhs .- c.rhs .>= M_l .* (1 .- z))
    else
        @constraint(m, c.lhs - c.rhs <= M_u * (1 - z))
        @constraint(m, c.lhs - c.rhs >= M_l * (1 - z))
    end
end 

function add_indicator!(m, i1::Implication, i2::Implication)
    z = @variable(m, category=:Bin, basename="z")
    implies!(m, z, i1.lhs)
    implies!(m, z, i1.rhs)
    implies!(m, 1 - z, i2.lhs)
    implies!(m, 1 - z, i2.rhs)
end

function disjunction!(m::Model, i1::Implication, i2::Implication)
    push!(get!(m.ext, :indicators, []), Disjunction([i1, i2]))
end

function setup_indicator!(m::Model, imp::Implication)
    sat = satisfied(imp.lhs)
    comp = complement(imp.lhs)
    if sat == yes
        require!(m, imp.lhs)
        require!(m, imp.rhs)
    elseif sat == no
        require!(m, comp)
    else
        @assert sat == maybe
        z = @variable(m, category=:Bin, basename="z")
        implies!(m, z, imp.lhs)
        implies!(m, z, imp.rhs)
        implies!(m, 1 - z, comp)
    end
end

function setup_indicator!(m::Model, d::Disjunction)
    @assert length(d.members) == 2
    setup_disjunction!(m, d.members[1], d.members[2])
end

function setup_disjunction!(m::Model, i1::Implication, i2::Implication)
    s1 = satisfied(i1.lhs)
    s2 = satisfied(i2.lhs)
    if s1 == yes || (s1 == maybe && s2 == no)
        require!(m, i1.lhs)
        require!(m, i1.rhs)
    elseif s2 == yes || (s1 == no && s2 == maybe)
        require!(m, i2.lhs)
        require!(m, i2.rhs)
    elseif s1 == no && s2 == no
        error("Neither $(i1.rhs) nor $(i2.rhs) can be satisfied using the values currently set to the model variables")
    else
        add_indicator!(m, i1, i2)
    end
end

function _setup_indicators!(m::Model)
    for x in get(m.ext, :indicators, [])
        setup_indicator!(m, x)
    end
    empty!(m.ext[:indicators])
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
    setvalue(assignment.first, assignment.second)
    f()
    setvalue(assignment.first, prev)
end

function with_assignment!(f::Function, m::Model, assignment::Pair{<:AbstractArray{Variable}, <:AbstractArray{<:Number}})
    prev = _getvalue.(assignment.first)
    setvalue.(assignment.first, assignment.second)
    f()
    setvalue.(assignment.first, prev)
end

function setup_indicators!(m::Model, assignment, assignments...)
    with_assignment!(m, assignment) do
        _setup_indicators!(m, assignments...)
    end
    m
end

function Base.ifelse(c::Conditional, v1, v2)
    @assert size(v1) == size(v2)
    m = getmodel(c)
    y = @variable(m, y, basename="y")
    setlowerbound.(y, min.(lowerbound.(v1), lowerbound.(v2)))
    setupperbound.(y, max.(upperbound.(v1), upperbound.(v2)))
    disjunction!(m,
        Implication(c, @conditional y == v1),
        Implication(complement(c), @conditional y == v2))
    y
end

function Base.ifelse(c::Conditional, v1::AbstractArray, v2::AbstractArray)
    @assert size(v1) == size(v2)
    m = getmodel(c)
    y = reshape(@variable(m, y[1:length(v1)], basename="y"), size(v1))
    setlowerbound.(y, min.(lowerbound.(v1), lowerbound.(v2)))
    setupperbound.(y, max.(upperbound.(v1), upperbound.(v2)))
    disjunction!(m,
        Implication(c, @conditional y == v1),
        Implication(complement(c), @conditional y == v2))
    y
end

macro disjunction(ex)
    if @capture(ex, if c1_; v1_; else v2_; end)
        cond_expr = _conditional(c1)
    else
        error("Could not parse: $ex")
    end
    quote
        if isa($(cond_expr).lhs - $(cond_expr).rhs, AbstractJuMPScalar)
            ifelse($(cond_expr), $(esc(v1)), $(esc(v2)))
        else
            $(esc(ex))
        end
    end
end
            

end