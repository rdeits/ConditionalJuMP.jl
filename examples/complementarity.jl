module Complementarity

using JuMP, ConditionalJuMP, Cbc
using Test
using Pkg

# A simple complementarity-based time-stepping rigid body simulation. All
# notation is taken from Stewart & Trinkle "An Implicit Time-Stepping Scheme for
# Rigid Body Dynamics with Coulomb Friction". This particular example solves
# for all N timesteps simultaneously. That's not actually necessary, but it makes
# the code a bit simpler to read.
#
# The model consists of a point mass (visualized as a brick) moving in two dimensions
# with gravity and a single planar surface at y = 0.

const h = 0.05
const μ = 0.5
const n = [0, 1]
const mass = 1.0
const g = [0, -9.81]
const D = [
    1 -1
    1  1
]
const k = size(D, 2)
const e = ones(k)

struct LCPUpdate{T}
    q::Vector{T}
    v::Vector{T}
    β::Vector{T}
    λ::T
    c_n::T
end

function JuMP.getvalue(up::LCPUpdate)
    LCPUpdate(getvalue.((up.q, up.v, up.β, up.λ, up.c_n))...)
end

function update(q, v, model)
    qnext = @variable(model, [1:length(q)], lowerbound=-10, basename="qnext", upperbound=10)
    vnext = @variable(model, [1:length(v)], lowerbound=-10, basename="vnext", upperbound=10)
    β = @variable(model,     [1:k],         lowerbound=0,   basename="β",     upperbound=100)
    λ = @variable(model,                    lowerbound=0,   basename="λ",     upperbound=100)
    c_n = @variable(model,                  lowerbound=0,   basename="c_n",   upperbound=100)

    @constraints model begin
        mass * (vnext - v) .== h * n * c_n .+ h * D * β .+ h * mass * g # (5)
        qnext - q .== h .* vnext # (6)
        n' * qnext >= 0 # (7)
        λ * e + D' * vnext .>= 0 # (8)
        μ * c_n - e' * β >= 0 # (9)
    end

    @disjunction(model, (n' * qnext == 0), (c_n == 0)) # (10)
    Dtv = D' * vnext
    for j in 1:k
        @disjunction(model, ((λ + Dtv[j]) == 0), (β[j] == 0)) # (11)
    end
    @disjunction(model, (μ * c_n - e' * β == 0), (λ == 0)) # (12)

    LCPUpdate(qnext, vnext, β, λ, c_n)
end

"""
Simulate the system using the LCP update. This creates and solves a small
model for every time step 1:N.
"""
function simulate(q0, v0, N)
    q, v = q0, v0
    results = LCPUpdate{Float64}[]
    for i in 1:N
        m = Model(solver=CbcSolver(logLevel=0))
        up = update(q, v, m)
        solve(m)
        push!(results, getvalue(up))
        q = results[end].q
        v = results[end].v
    end
    results
end

"""
Like simulate(), but solves for all N states in a single big
optimization, rather than solving each state separately. This
is more like what we would do if we had a control input we wanted
to optimize over
"""
function optimize(q0, v0, N)::Vector{LCPUpdate{Float64}}
    q, v = q0, v0
    m = Model(solver=CbcSolver(logLevel=0))
    results = []
    for i in 1:N
        up = update(q, v, m)
        push!(results, up)
        q = results[end].q
        v = results[end].v
    end
    solve(m)
    getvalue.(results)
end

q0 = [-1, 0.5]
v0 = [2, 0.5]
N = 30
results1 = simulate(q0, v0, N)
results2 = optimize(q0, v0, N)


@test all([r.q for r in results1] .≈ [r.q for r in results2])
@test all([r.v for r in results1] .≈ [r.v for r in results2])
@test all([r.λ for r in results1] .≈ [r.λ for r in results2])

q = [r.q for r in results1]
v = [r.v for r in results1]
@test q[end] ≈ [-0.16892500000000002, 0]
@test v[end] ≈ [0, 0]

if haskey(Pkg.installed(), "DrakeVisualizer")
    @eval using DrakeVisualizer;
    @eval using CoordinateTransformations
    @eval using GeometryTypes
    DrakeVisualizer.any_open_windows() || DrakeVisualizer.new_window()

    vis = Visualizer()[:block]
    setgeometry!(vis, HyperRectangle(Vec(-0.1, -0.1, 0), Vec(0.2, 0.2, 0.2)))

    for qi in q
        settransform!(vis, Translation(qi[1], 0, qi[2]))
        sleep(h)
    end
end

end
