using Test
using JuMP
using Cbc
using ConditionalJuMP
using Polyhedra
using LinearAlgebra

# In this example, we search for the point closest to the origin in the union
# of a list of convex polyhedra

# This implementation lets us add disjunctions and implications of the form
#   x in P
# where x is a vector and P is a Polyhedron
function ConditionalJuMP.Conditional(op::typeof(in), x::AbstractVector, P::HRepresentation)
    (&)([@?(h.a' * x <= h.β) for h in allhalfspaces(P)]...)
end

# A simple L1-norm objective we can minimize (since the Cbc
function l1norm_objective(x::AbstractVector{Variable})
    model = first(x).m
    y = @variable(model, [1:length(x)], basename="y", lowerbound=0)
    for i in 1:length(x)
        @constraint(model, y[i] >= x[i])
        @constraint(model, y[i] >= -x[i])
    end
    sum(y)
end

# P1 is a box from [-1.5, -1] to [-0.5, 1]
P1 = hrep(vcat(Matrix(I, 2, 2), -Matrix(I, 2, 2)), [-0.5, 1, 1.5, 1])

# P2 is a box from [1, -1] to [2, 1]
P2 = hrep(vcat(Matrix(I, 2, 2), -Matrix(I, 2, 2)), [2., 1, -1, 1])

m = Model(solver=CbcSolver(logLevel=0))
@variable(m, -5 <= x[1:2] <= 5)
@disjunction(m, x in P1, x in P2)
@objective(m, Min, l1norm_objective(x))

@test sum(m.colCat .== :Bin) == 1
solve(m)
x = getvalue(x)
@test x ≈ [-0.5, 0]
