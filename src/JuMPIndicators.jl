module JuMPIndicators

using JuMP
using JuMP: AbstractJuMPScalar
using MacroTools: @capture
using IntervalArithmetic: Interval, mid, radius

export @disjunction,
    @implies,
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

struct Condition{Op, T1, T2}
    op::Op
    lhs::T1
    rhs::T2
end

@enum TriState no yes maybe

function satisfied(c::Condition)
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

Base.show(io::IO, c::Condition) = print(io, "(", c.lhs, " ", c.op, " ", c.rhs, ")")

complement(c::Condition{typeof(<=)}) = Condition(c.op, -c.lhs, -c.rhs)

struct Implication{C1 <: Condition, C2 <: Condition}
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
                $(_condition(lhs)),
                $(_condition(rhs))))
    end
end


function _condition(ex::Expr)
    if @capture(ex, op_(lhs_, rhs_))
        quote
            Condition($(esc(op)), $(esc(lhs)), $(esc(rhs)))
        end
    else
        error("Could not parse: $ex. Expected `@condition(x <= 0)`")
    end
end

macro condition(ex)
    _condition(ex)
end

lowerbound(x::Number) = x
upperbound(x::Number) = x

lowerbound(x::AbstractJuMPScalar) = -upperbound(-x)

upperbound(x::Variable) = JuMP.getupperbound(x)

function upperbound(e::JuMP.GenericAffExpr{T, Variable}) where {T}
    intervals = [Interval(getlowerbound(v), getupperbound(v)) for v in e.vars]
    ex_bounds = e.coeffs' * intervals + e.constant
    mid(ex_bounds) + radius(ex_bounds)
end

require!(m::Model, c::Condition{typeof(<=)}) = @constraint(m, c.lhs <= c.rhs)
function require!(m::Model, c::Condition{typeof(==)})
    constraint = @constraint(m, c.lhs == c.rhs)
    setvalue(c.lhs, c.rhs)
    constraint
end

function implies!(m::Model, imp::Implication)
    comp = complement(imp.lhs)
    z = @variable(m, category=:Bin, basename="z")
    implies!(m, z, imp.lhs)
    implies!(m, z, imp.rhs)
    implies!(m, 1 - z, comp)
end

function implies!(m::Model, z::AbstractJuMPScalar, c::Condition{typeof(<=)})
    g = c.lhs - c.rhs
    M = upperbound(g)
    @constraint m c.lhs <= c.rhs + M * (1 - z)
end 

function implies!(m::Model, z::AbstractJuMPScalar, c::Condition{typeof(==)})
    g = c.lhs - c.rhs
    M_u = upperbound(g)
    @assert isfinite(M_u)
    @constraint(m, c.lhs - c.rhs <= M_u * (1 - z))
    M_l = lowerbound(g)
    @assert isfinite(M_l)
    @constraint(m, c.lhs - c.rhs >= M_l * (1 - z))
end 

function add_indicator!(m, i1::Implication, i2::Implication)
    z = @variable(m, category=:Bin, basename="z")
    implies!(m, z, i1.lhs)
    implies!(m, z, i1.rhs)
    implies!(m, 1 - z, i2.lhs)
    implies!(m, 1 - z, i2.rhs)
end

function disjunction!(m::Model, i1::Implication, i2::Implication)
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
    nothing
end

macro disjunction(ex)
    body, cond_expr = if @capture(ex, if c1_; v1_; else v2_; end)
        cond_expr = _condition(c1)
        quote
            cond = $(_condition(c1))
            comp = complement(cond)
            m = getmodel(cond.lhs)
            y = $(Expr(:macrocall, Symbol("@variable"), :m, Expr(:(=), esc(:basename), "y")))
            setlowerbound(y, min(lowerbound($(esc(v1))), lowerbound($(esc(v2)))))
            setupperbound(y, max(upperbound($(esc(v1))), upperbound($(esc(v2)))))
            disjunction!(m, 
                Implication(cond, Condition(==, y, $(esc(v1)))),
                Implication(comp, Condition(==, y, $(esc(v2)))))
            y
        end, cond_expr
    else
        error("Could not parse: $ex")
    end
    quote
        if isa($(cond_expr).lhs, AbstractJuMPScalar)
            $body
        else
            $(esc(ex))
        end
    end
end
            

end