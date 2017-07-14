module JuMPIndicators

using JuMP
using JuMP: AbstractJuMPScalar
using MacroTools: @capture
using IntervalArithmetic: Interval, mid, radius

getmodel(x::JuMP.Variable) = x.m
getmodel(x::JuMP.GenericAffExpr) = x.vars[1].m

struct Condition{Op, T1, T2}
    op::Op
    lhs::T1
    rhs::T2
end

_getvalue(x::AbstractJuMPScalar) = getvalue(x)
_getvalue(x::Number) = x

function _getvalue(c::Condition)
    lhs = _getvalue(c.lhs)
    rhs = _getvalue(c.rhs)
    @assert !isnan(lhs)
    @assert !isnan(rhs)
    c.op(lhs, rhs)
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

function _condition(ex::Expr)
    if @capture(ex, op1_(l1_, r1_) => op2_(l2_, r2_))
        quote
            Implication(
                Condition($(esc(op1)), $(esc(l1)), $(esc(r1))),
                Condition($(esc(op2)), $(esc(l2)), $(esc(r2))))
                
        end
    elseif @capture(ex, op_(lhs_, rhs_))
        quote
            Condition($(esc(op)), $(esc(lhs)), $(esc(rhs)))
        end
    else
        error("Could not parse: $ex")
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

function implies!(m::Model, z::AbstractJuMPScalar, c::Condition{typeof(<=)})
    g = c.lhs - c.rhs
    M = upperbound(g)
    @constraint m c.lhs <= c.rhs + M * (1 - z)
end 

function implies!(m::Model, z::AbstractJuMPScalar, c::Condition{typeof(==)})
    g = c.lhs - c.rhs
    M_u = upperbound(g)
    @constraint(m, c.lhs - c.rhs <= M_u * (1 - z))
    M_l = -upperbound(-g)
    @constraint(m, c.lhs - c.rhs >= M_l * (1 - z))
end 

function setup_disjunction_binary!(m, d::Disjunction)
    @assert length(d.members) == 2
    z = @variable(m, category=:Bin, basename="z")
    implies!(m, z, d.members[1].lhs)
    implies!(m, z, d.members[1].rhs)
    implies!(m, 1 - z, d.members[2].lhs)
    implies!(m, 1 - z, d.members[2].rhs)
    z
end

const Assignment = Pair{<:AbstractVector{Variable}, <:AbstractVector{<:Number}}

function with_assignments(f::Function, m::Model, assignments::Assignment...)
    for assignment in assignments
        JuMP.setvalue.(assignment.first, assignment.second)
        f()
    end
end

function apply_disjunction!(m, d::Disjunction)
    for imp in d.members
        if _getvalue(imp.lhs)
            require!(m, imp.lhs)
            require!(m, imp.rhs)
            break
        end
    end
end

setup_disjunctions!(m::Model) = setup_disjunction_binary!.(m, get(m.ext, :disjunctions, []))

function setup_disjunctions!(m::Model, assignments::Assignment...)
    with_assignments(m, assignments...) do
        apply_disjunction!.(m, get(m.ext, :disjunctions, []))
    end
end

function disjunction!(m::Model, i1::Implication, i2::Implication)
    push!(get!(m.ext, :disjunctions, Disjunction[]), Disjunction([i1, i2]))
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