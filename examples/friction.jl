using JuMP, ConditionalJuMP, Cbc
using Test

const viscosity = 100
const stiffness = 100
const penetration = 0.1
const normal_force = stiffness * penetration
const μ = 0.5
const Δt = 0.05

# A very simple stick-slip dynamics. Frictional force is equal to
# -(viscosity * velocity), clipped to lie within the friction cone
# at ±(μ * normal_force).
function dynamics(x)
    q = x[1]
    v = x[2]
    viscous_force = -viscosity * v
    frictional_force = @switch(
        (viscous_force ≤ -μ * normal_force)                                        => -μ * normal_force,
        ((viscous_force ≥ -μ * normal_force) & (viscous_force ≤ μ * normal_force)) => viscous_force,
        (viscous_force ≥ μ * normal_force)                                         => μ * normal_force
    )
    ẋ = [v, frictional_force]
    ẋ
end

# Naive forward-euler discretization of the continuous dynamics
function update(x)
    ẋ = dynamics(x)
    x .+ ẋ .* Δt
end

# Simulate forward using the given dynamics to get a trajectory of states
N = 20
x0 = [0, 3.0]
xsim = [x0]
for i in 2:N
    push!(xsim, update(xsim[end]))
end

# Now set up a mixed-integer program to solve for all N states simultaneously
m = Model(solver=CbcSolver(logLevel=0))
xvars = [@variable(m, [1:2], basename="x", lowerbound=-4, upperbound=4) for i in 1:N]
@constraint(m, xvars[1] .== x0)
for i in 2:N
    @constraint(m, xvars[i] .== update(xvars[i - 1]))
end
warmstart!(m)
solve(m)
xvals = getvalue.(xvars)

# Verify that the solution to the mixed-integer program is exactly the same as
# the simulation
@test all([xvals[i] ≈ xsim[i] for i in 1:N])

expected = Array{Float64,1}[[0.0, 3.0], [0.15, 2.75], [0.2875, 2.5], [0.4125, 2.25], [0.525, 2.0], [0.625, 1.75], [0.7125, 1.5], [0.7875, 1.25], [0.85, 1.0], [0.9, 0.75], [0.9375, 0.5], [0.9625, 0.25], [0.975, 0.0], [0.975, 0.0], [0.975, 0.0], [0.975, 0.0], [0.975, 0.0], [0.975, 0.0], [0.975, 0.0], [0.975, 0.0]]
@test all([xvals[i] ≈ expected[i] for i in 1:N])
@test all([xsim[i] ≈ expected[i] for i in 1:N])
