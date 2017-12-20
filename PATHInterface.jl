module PATHInterface

using JuMP
using PATHSolver

linear_constraints(model::Model) = model.linconstr
lowerbound(r::JuMP.GenericRangeConstraint) = r.lb
upperbound(r::JuMP.GenericRangeConstraint) = r.ub
is_equality(r::JuMP.GenericRangeConstraint) = lowerbound(r) == upperbound(r)

struct CannotConstructLCP <: Exception
    msg::String
end

# struct PartialLCP{T}
#     lb::Vector{T}
#     ub::Vector{T}
#     q::Vector{T}
#     M_rows::Vector{Cint}
#     M_cols::Vector{Cint}
#     M_data::Vector{T}

#     function PartialLCP(lb::AbstractVector{T}, ub::AbstractVector{T}) where T
#         new{T}(lb, ub, zeros(length(lb)), Cint[], Cint[], T[])
#     end
# end

struct LCP{T}
    lb::Vector{T}
    ub::Vector{T}
    q::Vector{T}
    M::SparseMatrixCSC{T, Cint}
end

# function LCP(partial::PartialLCP)
#     n = length(partial.lb)
#     @assert length(partial.ub) == n
#     @assert length(partial.q) == n
#     M = sparse(partial.M_rows, partial.M_cols, partial.M_data, n, n)
#     LCP(partial.lb, partial.ub, partial.q, M)
# end

# function add_equality!(lcp::PartialLCP, terms::JuMP.GenericAffExpr, value::Number)
#     push!(lcp.lb, -Inf)
#     push!(lcp.ub, Inf)
#     push!(lcp.q, terms.constant - value)
#     row = length(lcp.lb)
#     for i in eachindex(terms.vars)
#         push!(lcp.M_cols, terms.vars[i].col)
#         push!(lcp.M_rows, row)
#         push!(lcp.M_data, terms.coeffs[i])
#     end
# end

# function add_slack!(lcp::PartialLCP)
#     push!(lcp.lb, 0)
#     push!(lcp.ub, Inf)
#     push!(lcp.q, 0)
#     return length(lcp.lb)
# end

# function build_lcp(model::Model)
#     lcp = PartialLCP(copy(model.colLower), copy(model.colUpper))
    
#     iszero(getobjective(model)) || throw(CannotConstructLCP("LCP must not have an objective"))
    
#     for constraint in linear_constraints(model)
#         if !is_equality(constraint)
#             if lowerbound(constraint) != -Inf
#                 # Create a slack variable s >= 0 such that (terms - s) == lb
                
#                 s_idx = add_slack!(lcp)
#                 # Create constraint terms == lb
#                 add_equality!(lcp, constraint.terms, lowerbound(constraint))
#                 # then modify that constraint to turn it into (terms - s) == lb
#                 push!(lcp.M_rows, length(lcp.lb))
#                 push!(lcp.M_cols, s_idx)
#                 push!(lcp.M_data, -1)
#             end
#             if upperbound(constraint) != Inf
#                 # Create a slack variable s >= 0 such that (terms + s) == ub
                
#                 s_idx = add_slack!(lcp)
#                 # Create constraint terms == ub
#                 add_equality!(lcp, constraint.terms, upperbound(constraint))
#                 # then modify that constraint to turn it into (terms + s) == ub
#                 push!(lcp.M_rows, length(lcp.lb))
#                 push!(lcp.M_cols, s_idx)
#                 push!(lcp.M_data, 1)
#             end
#         else
#             add_equality!(lcp, constraint.terms, upperbound(constraint))
#         end
#     end      
        
#     LCP(lcp)
# end


import MathProgBase.SolverInterface
SI = SolverInterface

struct PATHLCPSolver <: SI.AbstractMathProgSolver
end

mutable struct PATHLCPModel <: SI.AbstractLinearQuadraticModel
    lcp::Nullable{LCP{Cdouble}}
    z::Nullable{Vector{Cdouble}}
    F::Nullable{Vector{Cdouble}}
    status::Nullable{Symbol}
end

SI.LinearQuadraticModel(s::PATHLCPSolver) = PATHLCPModel(nothing, nothing, nothing, nothing)

function standard_lp_form(A::AbstractMatrix{T}, lb, ub, constr_lb, constr_ub) where T
    nc, nv = size(A)
    num_slacks = sum(1:size(A, 1)) do i
        if constr_lb[i] == constr_ub[i]
            0
        else
            1
        end
    end

    A = hcat(A, spzeros(nc, num_slacks))
    lb = vcat(lb, zeros(num_slacks))
    ub = vcat(ub, fill(Inf, num_slacks))
    constr_lb = copy(constr_lb)
    constr_ub = copy(constr_ub)

    slack_idx = 1
    for i in 1:size(A, 1)
        if constr_lb[i] == constr_ub[i]
            continue
        elseif isfinite(constr_lb[i]) && isfinite(constr_ub[i])
            throw(CannotConstructLCP("Two-sided linear constraints (lb <= x <= ub) are not supported. Please convert this to two one-sided constraints."))
        elseif isfinite(constr_lb[i])
            A[i, nv + slack_idx] = -1
            constr_ub[i] = constr_lb[i]
        else
            @assert isfinite(constr_ub[i])
            A[i, nv + slack_idx] = 1
            constr_lb[i] = constr_ub[i]
        end
        slack_idx += 1
    end
    @assert slack_idx == num_slacks + 1
    A, lb, ub, constr_lb, constr_ub
end

function SI.loadproblem!(m::PATHLCPModel, A, lb, ub, obj, constr_lb, constr_ub, sense)
    if !all(iszero, obj)
        throw(CannotConstructLCP("LCP must not have an objective"))
    end
    A, lb, ub, constr_lb, constr_ub = standard_lp_form(A, lb, ub, constr_lb, constr_ub)
    @assert constr_lb == constr_ub
    @assert length(lb) == length(ub) == size(A, 2)
    nc = size(A, 1)
    nv = size(A, 2)

    m.lcp = LCP{Cdouble}(
        vcat(lb, fill(-Inf, nc)),
        vcat(ub, fill(Inf, nc)),
        vcat(zeros(nv), .-constr_lb),
        [spzeros(nv, nv + nc); 
             A   spzeros(nc, nc)]
        )
end

function SI.optimize!(m::PATHLCPModel)
    lcp = get(m.lcp)
    m.status, m.z, m.F = solveLCP(z -> lcp.q + lcp.M * z, lcp.M, lcp.lb, lcp.ub)
end

# TODO: is this the right mapping?
const status_table = Dict(
      :Solved => :Optimal,                          # 1 - solved
      :StationaryPointFound => :Infeasible,            # 2 - stationary point found
      :MajorIterationLimit => :UserLimit,             # 3 - major iteration limit
      :CumulativeMinorIterationLimit => :UserLimit,   # 4 - cumulative minor iteration limit
      :TimeLimit => :UserLimit,                       # 5 - time limit
      :UserInterrupt => :UserLimit,                   # 6 - user interrupt
      :BoundError => :Error,                      # 7 - bound error (lb is not less than ub)
      :DomainError => :Error,                     # 8 - domain error (could not find a starting point)
      :InternalError => :Error                    # 9 - internal error
      )

SI.status(m::PATHLCPModel) = status_table[get(m.status)]
SI.getobjval(m::PATHLCPModel) = 0.0
SI.getsolution(m::PATHLCPModel) = get(m.z)

end