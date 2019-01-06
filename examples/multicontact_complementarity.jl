module Complementarity

using Polyhedra
using StaticArrays
using JuMP, ConditionalJuMP, Cbc
using Test
using Pkg

rot2(θ) = SMatrix{2, 2}(cos(θ), -sin(θ), sin(θ), cos(θ))

struct Obstacle{N, T, H <: HRepresentation{N, T}}
    interior::H
    contact_face::HalfSpace{N, T}
end

struct Environment{N, T, H1 <: HRepresentation{N, T}, H2 <: HRepresentation{N, T}}
    obstacles::Vector{Obstacle{N, T, H1}}
    free_regions::Vector{H2}
end

function contact_basis(face::HalfSpace{2})
    θ = atan(μ)
    R = rot2(θ)
    hcat(R * face.a, R' * face.a)
end


contact_basis(obs::Obstacle) = contact_basis(obs.contact_face)

function ConditionalJuMP.Conditional(op::typeof(in), x::AbstractVector, P::HRepresentation)
    ConditionalJuMP.Conditional(&, [@?(P.A[i, :]' * x <= P.b[i]) for i in 1:length(P)]...)
end


# A simple complementarity-based time-stepping rigid body simulation. All
# notation is taken from Stewart & Trinkle "An Implicit Time-Stepping Scheme for
# Rigid Body Dynamics with Coulomb Friction".

const h = 0.05
const μ = 0.5
const n = [0, 1]
const mass = 1.0
const g = [0, -9.81]

struct ContactResult{T, Tf}
    β::Vector{T}
    λ::T
    c_n::T
    contact_force::Tf
end

JuMP.getvalue(c::ContactResult) = ContactResult(getvalue.((c.β, c.λ, c.c_n, c.contact_force))...)

struct LCPUpdate{T, Tf}
    q::Vector{T}
    v::Vector{T}
    contacts::Vector{ContactResult{T, Tf}}
end

JuMP.getvalue(up::LCPUpdate) =
    LCPUpdate(getvalue.((up.q, up.v))..., getvalue.(up.contacts))

function contact_force(qnext, vnext, obstacle::Obstacle, model::Model)
    n = obstacle.contact_face.a
    D = contact_basis(obstacle)
    k = size(D, 2)

    β = @variable(model,   [1:k], lowerbound=0,   basename="β",     upperbound=100)
    λ = @variable(model,          lowerbound=0,   basename="λ",     upperbound=100)
    c_n = @variable(model,        lowerbound=0,   basename="c_n",   upperbound=100)

    @constraints model begin
        λ .+ D' * vnext .>= 0 # (8)
        μ * c_n .- sum(β) >= 0 # (9)
    end

    @disjunction(model, (n' * qnext - obstacle.contact_face.β == 0), (c_n == 0)) # (10)
    Dtv = D' * vnext
    for j in 1:k
        @disjunction(model, ((λ + Dtv[j]) == 0), β[j] == 0) # (11)
    end
    @disjunction(model, (μ * c_n - sum(β) == 0), (λ == 0)) # (12)

    contact_force = c_n * n .+ D * β
    ContactResult(β, λ, c_n, contact_force)
end

function update(q, v, env::Environment, model::Model)
    qnext = @variable(model, [1:length(q)], lowerbound=-10, basename="qnext", upperbound=10)
    vnext = @variable(model, [1:length(v)], lowerbound=-10, basename="vnext", upperbound=10)

    contacts = [contact_force(qnext, vnext, obs, model) for obs in env.obstacles]
    total_force = mass * g + sum([c.contact_force for c in contacts])

    @constraints model begin
        mass * (vnext - v) .== h * total_force # (5)
        qnext - q .== h .* vnext # (6)
    end

    ConditionalJuMP.disjunction!(
        model,
        [@?(qnext ∈ P) for P in env.free_regions]) # (7)

    LCPUpdate(qnext, vnext, contacts)
end

function simulate(q0, v0, env::Environment, N)
    q, v = q0, v0
    results = LCPUpdate{Float64}[]
    for i in 1:N
        m = Model(solver=CbcSolver())
        up = update(q, v, env, m)
        solve(m)
        push!(results, getvalue(up))
        q = results[end].q
        v = results[end].v
    end
    results
end

function optimize(q0, v0, env::Environment, N::Integer)::Vector{LCPUpdate{Float64}}
    q, v = q0, v0
    m = Model(solver=CbcSolver())
    results = []
    for i in 1:N
        up = update(q, v, env, m)
        push!(results, up)
        q = results[end].q
        v = results[end].v
    end
    solve(m)
    getvalue.(results)
end

function JuMP.setvalue(contact::ContactResult{<:JuMP.AbstractJuMPScalar}, seed::ContactResult{<:Number})
    setvalue(contact.β, seed.β)
    setvalue(contact.λ, seed.λ)
    setvalue(contact.c_n, seed.c_n)
    @assert getvalue(contact.contact_force) ≈ seed.contact_force
end

function JuMP.setvalue(up::LCPUpdate{<:JuMP.AbstractJuMPScalar}, seed::LCPUpdate{<:Number})
    setvalue(up.q, seed.q)
    setvalue(up.v, seed.v)
    setvalue.(up.contacts, seed.contacts)
end

function optimize(q0, v0, env::Environment, seed::Vector{<:LCPUpdate})
    q, v = q0, v0
    m = Model(solver=CbcSolver())
    results = []
    for i in 1:N
        up = update(q, v, env, m)
        setvalue(up, seed[i])
        push!(results, up)
        q = results[end].q
        v = results[end].v
    end
    warmstart!(m, true)
    @assert sum(m.colCat .== :Bin) == 0
    solve(m)
    getvalue.(results)
end


env = Environment(
    [
        Obstacle(
            SimpleHRepresentation{2, Float64}([0 1], [0]),
            HalfSpace{2, Float64}([0, 1], 0)
        ),
        Obstacle(
            SimpleHRepresentation{2, Float64}([-1 0], [-0.2]),
            HalfSpace{2, Float64}([-1, 0], -0.2)
        )
    ],
    [
        SimpleHRepresentation{2, Float64}(
            [0 -1;
             1 0],
            [0, 0.2])
    ]
)

q0 = [-0.5, 0.5]
v0 = [3, -1.5]
N = 20
results1 = simulate(q0, v0, env, N)
results2 = optimize(q0, v0, env, N)
@test all([r1.q ≈ r2.q for (r1, r2) in zip(results1, results2)])

results_seeded = optimize(q0, v0, env, results1)
@test all([r1.q ≈ r2.q for (r1, r2) in zip(results1, results_seeded)])

if haskey(Pkg.installed(), "DrakeVisualizer")
    @eval using DrakeVisualizer;
    @eval using CoordinateTransformations
    DrakeVisualizer.any_open_windows() || DrakeVisualizer.new_window()

    vis = Visualizer()[:block]
    setgeometry!(vis, HyperRectangle(Vec(-0.1, -0.1, 0), Vec(0.2, 0.2, 0.2)))

    q = [r.q for r in results1]
    for qi in q
        settransform!(vis, Translation(qi[1], 0, qi[2]))
        sleep(h)
    end
end

end
