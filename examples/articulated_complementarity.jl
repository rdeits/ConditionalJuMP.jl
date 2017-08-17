module Complementarity

using Polyhedra
using StaticArrays
using JuMP, ConditionalJuMP, Cbc
using Base.Test
using RigidBodyDynamics
using RigidBodyDynamics: colwise
using Rotations
using ForwardDiff

struct Obstacle{T, H <: HRepresentation{3, T}}
    interior::H
    contact_face::HalfSpace{3, T}
    μ::T
end

struct ContactEnvironment{P <: Point3D, T, H <: HRepresentation{3, T}}
    points::Vector{P}
    obstacles::Vector{Obstacle{T, H}}
    free_regions::Vector{H}
end

struct Environment{B <: RigidBody, C <: ContactEnvironment}
    contacts::Dict{B, C}
end

function contact_basis(face::HalfSpace{3}, μ)
    θ = atan(μ)
    R = RotY(θ)
    hcat(R * face.a, R' * face.a)
end

contact_basis(obs::Obstacle) = contact_basis(obs.contact_face, obs.μ)

function ConditionalJuMP.Conditional(op::typeof(in), x::AbstractVector, P::HRepresentation)
    ConditionalJuMP.Conditional(&, [@?(P.A[i, :]' * x <= P.b[i]) for i in 1:length(P)]...)
end

struct ContactResult{T, Tf}
    β::Vector{T}
    λ::T
    c_n::T
    contact_force::Tf
end

JuMP.getvalue(c::ContactResult) = ContactResult(getvalue.((c.β, c.λ, c.c_n, c.contact_force))...)
function JuMP.setvalue(contact::ContactResult{<:JuMP.AbstractJuMPScalar}, seed::ContactResult{<:Number})
    setvalue(contact.β, seed.β)
    setvalue(contact.λ, seed.λ)
    setvalue(contact.c_n, seed.c_n)
    @assert getvalue(contact.contact_force) ≈ seed.contact_force
end

JuMP.getvalue(f::FreeVector3D) = FreeVector3D(f.frame, getvalue(f.v))

struct JointLimitResult{T, Tf <: AbstractVector}
    λ::T
    generalized_force::Tf
end

JuMP.getvalue(r::JointLimitResult) = JointLimitResult(getvalue.((r.λ, r.generalized_force))...)
function JuMP.setvalue(r::JointLimitResult{<:JuMP.AbstractJuMPScalar}, seed::JointLimitResult{<:Number})
    setvalue(r.λ, seed.λ)
    @assert getvalue(r.generalized_force) ≈ seed.generalized_force
end

function JuMP.getvalue(x::MechanismState{<:JuMP.AbstractJuMPScalar})
    MechanismState(x.mechanism, getvalue(configuration(x)), getvalue(velocity(x)), getvalue(additional_state(x)))
end

struct LCPUpdate{T, M <: MechanismState{T}, Tf}
    state::M
    contacts::Vector{ContactResult{T, Tf}}
    # joint_contacts::Vector{JointLimitResult{T, Tf}}
end

# JuMP.getvalue(up::LCPUpdate) =
#     LCPUpdate(getvalue(up.state), getvalue.(up.contacts), getvalue.(up.joint_contacts))
JuMP.getvalue(up::LCPUpdate) =
    LCPUpdate(getvalue(up.state), getvalue.(up.contacts))

function JuMP.setvalue(up::LCPUpdate{<:JuMP.AbstractJuMPScalar}, seed::LCPUpdate{<:Number})
    setvalue(up.state, seed.state)
    setvalue.(up.contacts, seed.contacts)
    setvalue.(up.joint_contacts, seed.joint_contacts)
end

function leg_position_in_world(q)
    q[1:2] + [0, -1] * q[3]
end

function leg_velocity_in_world(v)
    v[1:2] + [0, -1] * v[3]
end

struct ContactPoint{Tb <: RigidBody, Tp <: Point3D}
    body::Tb
    point::Tp
end

function resolve_contact(xnext::MechanismState, contact_point::ContactPoint, obstacle::Obstacle, model::Model, x_dynamics::MechanismState{<:Number})
    n = obstacle.contact_face.a
    D = contact_basis(obstacle)
    k = size(D, 2)

    β = @variable(model,   [1:k], lowerbound=0,   basename="β",     upperbound=100)
    λ = @variable(model,          lowerbound=0,   basename="λ",     upperbound=100)
    c_n = @variable(model,        lowerbound=0,   basename="c_n",   upperbound=100)

    function separation_in_world(x)
        q = x[1:num_positions(xnext)]
        v = x[(num_positions(xnext)+1):end]
        x_diff = MechanismState(xnext.mechanism, q, v)
        point_in_world = transform_to_root(x_diff, contact_point.point.frame) * contact_point.point
        separation = n' * point_in_world.v - obstacle.contact_face.β
    end

    separation = separation_in_world(state_vector(x_dynamics)) + (state_vector(xnext) - state_vector(x_dynamics))' * ForwardDiff.gradient(separation_in_world, state_vector(x_dynamics))

    function contact_velocity_in_world(x)
        q = x[1:num_positions(xnext)]
        v = x[(num_positions(xnext)+1):end]
        x_diff = MechanismState(xnext.mechanism, q, v)
        point_in_world = transform_to_root(x_diff, contact_point.point.frame) * contact_point.point
        contact_velocity = point_velocity(twist_wrt_world(x_diff, contact_point.body), point_in_world).v
    end

    contact_velocity = contact_velocity_in_world(state_vector(x_dynamics)) + ForwardDiff.jacobian(contact_velocity_in_world, state_vector(x_dynamics)) * (state_vector(xnext) - state_vector(x_dynamics))

    @constraints model begin
        λ .+ D' * contact_velocity .>= 0 # (8)
        obstacle.μ * c_n .- sum(β) >= 0 # (9)
    end

    @disjunction(model, (separation == 0), (c_n == 0)) # (10)
    Dtv = D' * contact_velocity
    for j in 1:k
        @disjunction(model, ((λ + Dtv[j]) == 0), β[j] == 0) # (11)
    end
    @disjunction(model, (obstacle.μ * c_n - sum(β) == 0), (λ == 0)) # (12)

    contact_force = FreeVector3D(root_frame(xnext.mechanism), c_n * n .+ D * β)
    ContactResult(β, λ, c_n, contact_force)
end

function joint_limit(qnext, vnext, a::AbstractVector, b::Number, model::Model)
    λ = @variable(model, lowerbound=0, upperbound=100, basename="λ")
    separation = a' * qnext - b
    @constraint model separation <= 0
    @disjunction(model, separation == 0, λ == 0)

    JointLimitResult(λ, -λ * a)
end

function join_limits(qnext, vnext, limits::SimpleHRepresentation, model::Model)
    [joint_limit(qnext, vnext, limits.A[i, :], limits.b[i], model) for i in 1:length(limits)]
end

function update(x::MechanismState{X, M}, u, env::Environment, Δt::Real, model::Model, x_dynamics=x) where {X, M}
    mechanism = x.mechanism
    world = root_body(mechanism)
    qnext = @variable(model, [1:num_positions(x)], lowerbound=-10, basename="qnext", upperbound=10)
    vnext = @variable(model, [1:num_velocities(x)], lowerbound=-10, basename="vnext", upperbound=10)
    xnext = MechanismState(mechanism, qnext, vnext)

    contact_results = []
    externalwrenches_list = []
    for (body, contact_env) in env.contacts
        geo_jac = geometric_jacobian(x_dynamics, path(mechanism, body, world))
        wrenches = []

        for contact_point in contact_env.points
            for obs in contact_env.obstacles
                result = resolve_contact(xnext, ContactPoint(body, contact_point), obs, model, x_dynamics)
                push!(contact_results, result)
                push!(wrenches, Wrench(
                    transform_to_root(x_dynamics, contact_point.frame) * contact_point, 
                    result.contact_force))
            end

            function _point_in_world(x)
                q = x[1:num_positions(xnext)]
                v = x[(num_positions(xnext)+1):end]
                x_diff = MechanismState(xnext.mechanism, q, v)
                point_in_world = transform_to_root(x_diff, contact_point.frame) * contact_point
                point_in_world.v
            end

            point_in_world = _point_in_world(state_vector(x_dynamics)) + ForwardDiff.jacobian(_point_in_world, state_vector(x_dynamics)) * (state_vector(xnext) - state_vector(x_dynamics))

            ConditionalJuMP.disjunction!(model,
                [@?(point_in_world ∈ P) for P in contact_env.free_regions]) # (7)
        end
        push!(externalwrenches_list, (body => sum(wrenches)))
    end
    externalwrenches = Dict(externalwrenches_list)
    contact_results_type = typeof(contact_results[1])
    contact_results_typed = convert(Vector{contact_results_type}, contact_results)


    H = mass_matrix(x_dynamics)
    bias = dynamics_bias(x_dynamics, externalwrenches)

    @constraint(model, H * (vnext - velocity(x)) .== Δt * (u .- bias)) # (5)

    function _config_derivative(v)
        q = oftype(v, configuration(x_dynamics))
        x_diff = MechanismState(mechanism, q, v)
        configuration_derivative(x_diff)
    end

    config_derivative = ForwardDiff.jacobian(_config_derivative, velocity(x_dynamics)) * velocity(xnext)
    @constraint(model, qnext .- configuration(x) .== Δt .* config_derivative)

    LCPUpdate(xnext, contact_results_typed)

    # joint_limit_results = join_limits(qnext, vnext, SimpleHRepresentation([0. 0 1; 0 0 -1], [1.5, -0.5]), model)

    # internal_force = u + sum([r.generalized_force[3] for r in joint_limit_results])

    # LCPUpdate(qnext, vnext, contact_results, joint_limit_results)
end

function simulate(x0::MechanismState, controller, env::Environment, Δt::Real, N::Integer)
    results = []  # todo: type this
    x = x0
    for i in 1:N
        m = Model(solver=CbcSolver())
        u = controller(x)
        up = update(x, u, env, Δt, m)
        # up = update(q, v, u, env, m)
        solve(m)
        push!(results, getvalue(up))
        x = results[end].state
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

end