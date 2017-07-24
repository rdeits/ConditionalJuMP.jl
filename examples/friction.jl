using JuMP, ConditionalJuMP, Cbc
using Base.Test

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
x0 = [0, 3.0]
xs = [x0]
for i in 1:20
    push!(xs, update(xs[end]))
end

# Now set up a mixed-integer program to solve for all N states simultaneously
m = Model(solver=CbcSolver())
N = 20
xvars = [@variable(m, [1:2], basename="x", lowerbound=-4, upperbound=4) for i in 1:N]
@constraint(m, xvars[1] .== x0)
for i in 2:N
    @constraint(m, xvars[i] .== update(xvars[i - 1]))
end
setup_indicators!(m)
display(m)
solve(m)
xvals = getvalue.(xvars)

# Verify that the solution to the mixed-integer program is exactly the same as
# the simulation
@test all([xvals[i] ≈ xs[i] for i in 1:N])
