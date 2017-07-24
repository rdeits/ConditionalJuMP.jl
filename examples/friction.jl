using JuMP, ConditionalJuMP, Cbc
using Base.Test

const viscosity = 100
const stiffness = 100
const penetration = 0.1
const normal_force = stiffness * penetration
const μ = 0.5
const Δt = 0.05

function dynamics(x)
    q = x[1]
    v = x[2]
    viscous_force = -viscosity * v
    frictional_force = @switch(
        (viscous_force ≤ -μ * normal_force) => -μ * normal_force,
        ((viscous_force ≥ -μ * normal_force) & (viscous_force ≤ μ * normal_force)) => viscous_force,
        (viscous_force ≥ μ * normal_force) => μ * normal_force
    )
    ẋ = [v, frictional_force]
    ẋ
end  

x0 = [0, 3.0]
xs = [x0]
forces = []
for i in 1:20
    ẋ = dynamics(xs[end])
    push!(forces, ẋ[2])
    push!(xs, xs[end] .+ Δt .* ẋ)
end

m = Model(solver=CbcSolver())
N = 20
xvars = [@variable(m, [1:2], basename="x", lowerbound=-4, upperbound=4) for i in 1:N]
for i in 2:N
    @constraint(m, xvars[i] .== xvars[i - 1] .+ dynamics(xvars[i - 1]) .* Δt)
end
@constraint(m, xvars[1] .== x0)
setup_indicators!(m)
display(m)
solve(m)
xvals = getvalue.(xvars)

@test all([xvals[i] ≈ xs[i] for i in 1:N])
