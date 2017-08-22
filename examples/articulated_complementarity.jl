module Complementarity

using Polyhedra
using StaticArrays
using JuMP, ConditionalJuMP, Cbc
using JuMP: GenericAffExpr
using Base.Test
using RigidBodyDynamics
using RigidBodyDynamics: colwise
using Rotations
using ForwardDiff

struct Obstacle{T}
    frame::CartesianFrame3D
    interior::SimpleHRepresentation{3, T}
    contact_face::HalfSpace{3, T}
    μ::T
end

struct FreeRegion{T}
    frame::CartesianFrame3D
    interior::SimpleHRepresentation{3, T}
end

struct ContactEnvironment{T}
    points::Vector{Point3D{SVector{3, T}}}
    obstacles::Vector{Obstacle{T}}
    free_regions::Vector{FreeRegion{T}}
end

struct Environment{T}
    contacts::Dict{RigidBody{T}, ContactEnvironment{T}}
end

function contact_basis(obs::Obstacle)
    θ = atan(obs.μ)
    R = RotY(θ)
    SVector(
        FreeVector3D(obs.frame, R * obs.contact_face.a), 
        FreeVector3D(obs.frame, R' * obs.contact_face.a))
end

contact_normal(obs::Obstacle) = FreeVector3D(obs.frame, obs.contact_face.a)

function separation(obs::Obstacle, p::Point3D)
    @framecheck obs.frame p.frame
    n = contact_normal(obs)
    n.v' * p.v - obs.contact_face.β
end

Base.@pure ConditionalJuMP.isjump(::Point3D{<:AbstractArray{<:JuMP.AbstractJuMPScalar}}) = true

function ConditionalJuMP.Conditional(op::typeof(in), x::Point3D, P::FreeRegion)
    @framecheck(x.frame, P.frame)
    ConditionalJuMP.Conditional(&, [@?(P.interior.A[i, :]' * x.v <= P.interior.b[i]) for i in 1:length(P.interior)]...)
end

struct ContactResult{T, M}
    β::Vector{T}
    λ::T
    c_n::T
    point::Point3D{SVector{3, M}}
    obs::Obstacle{M}
end

_vec(f::FreeVector3D) = convert(Vector, f.v)
_vec(p::Point3D) = convert(Vector, p.v)

function contact_force(r::ContactResult)
    n = contact_normal(r.obs)
    D = contact_basis(r.obs)
    @framecheck(n.frame, D[1].frame)
    # r.c_n * n .+ D * r.β
    FreeVector3D(n.frame, r.c_n .* n.v .+ sum(broadcast.(*, _vec.(D), r.β)))
end

JuMP.getvalue(c::ContactResult) = ContactResult(getvalue.((c.β, c.λ, c.c_n))..., c.point, c.obs)
function JuMP.setvalue(contact::ContactResult{<:JuMP.AbstractJuMPScalar}, seed::ContactResult{<:Number})
    @assert contact.obs == seed.obs
    setvalue(contact.β, seed.β)
    setvalue(contact.λ, seed.λ)
    setvalue(contact.c_n, seed.c_n)
end

JuMP.getvalue(f::FreeVector3D) = FreeVector3D(f.frame, getvalue(f.v))

struct JointLimitResult{T, Tf}
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

struct LCPUpdate{T, M, S <: MechanismState{T, M}, I <:AbstractVector, J <: Joint, Tf}
    state::S
    input::I
    contacts::Dict{RigidBody{M}, Vector{ContactResult{T, M}}}
    joint_contacts::Dict{J, Vector{JointLimitResult{T, Tf}}}
end

JuMP.getvalue(p::Pair{<:RigidBody, <:AbstractVector{<:ContactResult}}) = p.first => getvalue.(p.second)
JuMP.getvalue(p::Pair{<:Joint, <:AbstractVector{<:JointLimitResult}}) = p.first => getvalue.(p.second)

_getvalue(x::AbstractVector{<:Number}) = x
_getvalue(x::AbstractVector{<:JuMP.AbstractJuMPScalar}) = getvalue(x)

JuMP.getvalue(up::LCPUpdate) =
    LCPUpdate(getvalue(up.state), _getvalue(up.input), map(getvalue, up.contacts), map(getvalue, up.joint_contacts))

JuMP.setvalue(d::Dict{<:Joint, <:Vector{<:JointLimitResult}}, seed::Dict) = [setvalue.(v1, v2) for (v1, v2) in zip(values(d), values(seed))]

function JuMP.setvalue(up::LCPUpdate{<:JuMP.AbstractJuMPScalar}, seed::LCPUpdate{<:Number})
    setvalue(up.state, seed.state)
    setvalue.(up.contacts, seed.contacts)
    setvalue(up.joint_contacts, seed.joint_contacts)
end

function resolve_contact(xnext::MechanismState, body::RigidBody, point::Point3D, obstacle::Obstacle, model::Model, x_dynamics::MechanismState{<:Number})
    D = contact_basis(obstacle)
    k = length(D)

    β = @variable(model,   [1:k], lowerbound=0,   basename="β",     upperbound=100)
    λ = @variable(model,          lowerbound=0,   basename="λ",     upperbound=100)
    c_n = @variable(model,        lowerbound=0,   basename="c_n",   upperbound=100)

    function _separation(x)
        q = x[1:num_positions(xnext)]
        v = x[(num_positions(xnext)+1):end]
        x_diff = MechanismState(xnext.mechanism, q, v)
        point_in_world = transform_to_root(x_diff, point.frame) * point
        separation(obstacle, point_in_world)
    end

    separation_from_obstacle = _separation(state_vector(x_dynamics)) + (state_vector(xnext) - state_vector(x_dynamics))' * ForwardDiff.gradient(_separation, state_vector(x_dynamics))

    function _contact_velocity(x)
        q = x[1:num_positions(xnext)]
        v = x[(num_positions(xnext)+1):end]
        x_diff = MechanismState(xnext.mechanism, q, v)
        point_in_world = transform_to_root(x_diff, point.frame) * point
        contact_velocity = point_velocity(twist_wrt_world(x_diff, body), point_in_world).v
    end

    contact_velocity = FreeVector3D(root_frame(xnext.mechanism), _contact_velocity(state_vector(x_dynamics)) + ForwardDiff.jacobian(_contact_velocity, state_vector(x_dynamics)) * (state_vector(xnext) - state_vector(x_dynamics)))

    D_transpose_times_v = [dot(d, contact_velocity) for d in D]

    @constraints model begin
        λ .+ D_transpose_times_v .>= 0 # (8)
        obstacle.μ * c_n .- sum(β) >= 0 # (9)
    end

    @disjunction(model, (separation_from_obstacle == 0), (c_n == 0)) # (10)
    for j in 1:k
        @disjunction(model, ((λ + D_transpose_times_v[j]) == 0), β[j] == 0) # (11)
    end
    @disjunction(model, (obstacle.μ * c_n - sum(β) == 0), (λ == 0)) # (12)

    ContactResult(β, λ, c_n, point, obstacle)
end

function resolve_joint_limit(xnext::MechanismState, joint::Joint, a::AbstractVector, b::Number, model::Model)
    λ = @variable(model, lowerbound=0, upperbound=100, basename="λ")
    q = configuration(xnext, joint)
    separation = a' * q - b
    @constraint model separation <= 0
    @disjunction(model, separation == 0, λ == 0)

    JointLimitResult(λ, -λ * a)
end

function resolve_joint_limits(xnext::MechanismState, joint::Joint, limits::HRepresentation, model::Model)
    [resolve_joint_limit(xnext, joint, limits.A[i, :], limits.b[i], model) for i in 1:length(limits)]
end

function update(x::MechanismState{X, M}, 
                u, 
                joint_limits::Associative{<:Joint, <:HRepresentation}, 
                env::Environment, 
                Δt::Real, 
                model::Model, 
                x_dynamics=x) where {X, M}
    mechanism = x.mechanism
    world = root_body(mechanism)
    qnext = @variable(model, [1:num_positions(x)], lowerbound=-10, basename="qnext", upperbound=10)
    vnext = @variable(model, [1:num_velocities(x)], lowerbound=-10, basename="vnext", upperbound=10)
    xnext = MechanismState(mechanism, qnext, vnext)

    contact_results = map(env.contacts) do item
        body, contact_env = item
        body => [resolve_contact(xnext, body, contact_point, obstacle, model, x_dynamics)
            for contact_point in contact_env.points for obstacle in contact_env.obstacles]
    end

    externalwrenches = map(contact_results) do item
        body, results = item
        body => sum([Wrench(transform_to_root(x_dynamics, result.point.frame) * result.point,
                    contact_force(result)) for result in results])
    end


    for (body, contact_env) in env.contacts
        for contact_point in contact_env.points
            function _point_in_world(x)
                q = x[1:num_positions(xnext)]
                v = x[(num_positions(xnext)+1):end]
                x_diff = MechanismState(xnext.mechanism, q, v)
                point_in_world = transform_to_root(x_diff, contact_point.frame) * contact_point
                point_in_world.v
            end

            position = Point3D(root_frame(mechanism), _point_in_world(state_vector(x_dynamics)) + ForwardDiff.jacobian(_point_in_world, state_vector(x_dynamics)) * (state_vector(xnext) - state_vector(x_dynamics)))

            ConditionalJuMP.disjunction!(model,
                [@?(position ∈ P) for P in contact_env.free_regions]) # (7)
        end
    end

    function _config_derivative(v)
        q = oftype(v, configuration(x_dynamics))
        x_diff = MechanismState(mechanism, q, v)
        configuration_derivative(x_diff)
    end

    jac_dq_wrt_v = ForwardDiff.jacobian(_config_derivative, velocity(x_dynamics))

    joint_limit_results = Dict([joint => resolve_joint_limits(xnext, joint, limits, model) for (joint, limits) in joint_limits])
    joint_limit_forces = zeros(GenericAffExpr{M, Variable}, num_velocities(x))
    for (joint, results) in joint_limit_results
        for result in results
            joint_limit_forces .+= (jac_dq_wrt_v')[:, parentindexes(configuration(x, joint))...] * result.generalized_force
        end
    end

    H = mass_matrix(x_dynamics)
    bias = dynamics_bias(x_dynamics, externalwrenches)
    config_derivative = jac_dq_wrt_v * velocity(xnext)

    @constraint(model, H * (vnext - velocity(x)) .== Δt * (u .+ joint_limit_forces .- bias)) # (5)
    @constraint(model, qnext .- configuration(x) .== Δt .* config_derivative) # (6)

    LCPUpdate(xnext, u, contact_results, joint_limit_results)
end

function simulate(x0::MechanismState, 
                  controller, 
                  joint_limits::Associative{<:Joint, <:HRepresentation}, 
                  env::Environment, 
                  Δt::Real, 
                  N::Integer)
    results = []  # todo: type this
    x = x0
    for i in 1:N
        m = Model(solver=CbcSolver())
        u = controller(x)
        up = update(x, u, joint_limits, env, Δt, m)
        solve(m)
        push!(results, getvalue(up))
        x = results[end].state
    end
    results
end

# TODO: 
# * record u in LCPUpdate
# * lots of cleanup
# * figure out a neater way to handle x_dynamics

function optimize(x0::MechanismState, 
                  joint_limits::Associative{<:Joint, <:HRepresentation}, 
                  env::Environment, 
                  Δt,
                  N::Integer,
                  solver=CbcSolver())
    x = x0
    m = Model(solver=solver)
    results = map(1:N) do i
        u = @variable(m, [1:num_velocities(x0)], basename="u_$i", lowerbound=-10, upperbound=10)
        up = update(x, u, joint_limits, env, Δt, m, x0)
        x = up.state
        up
    end
    m, results
    # solve(m)
    # getvalue.(results)
end

function optimize(x0::MechanismState, 
                  joint_limits::Associative{<:Joint, <:HRepresentation}, 
                  env::Environment, 
                  Δt,
                  seed::Vector{<:LCPUpdate})
    x = x0
    m = Model(solver=CbcSolver())
    results = map(1:N) do i
        u = @variable(m, [1:num_velocities(x0)], basename="u_$i", lowerbound=-10, upperbound=10)
        up = update(x, u, joint_limits, env, Δt, m, x0)
        setvalue(up, seed[i])
        x = up.state
        up
    end
    warmstart!(m, true)
    @assert sum(m.colCat .== :Bin) == 0
    m, results
    # solve(m)
    # getvalue.(results)
end

end