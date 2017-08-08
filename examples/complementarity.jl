using JuMP, ConditionalJuMP, Cbc
using Base.Test

# A simple complementarity-based time-stepping rigid body simulation. All
# notation is taken from Stewart & Trinkle "An Implicit Time-Stepping Scheme for
# Rigid Body Dynamics with Coulomb Friction". This particular example solves
# for all N timesteps simultaneously. That's not actually necessary, but it makes
# the code a bit simpler to read. 
#
# The model consists of a point mass (visualized as a brick) moving in two dimensions
# with gravity and a single planar surface at y = 0. 

N = 30
h = 0.05
μ = 0.5
n = [0, 1]
mass = 1.0
g = [0, -9.81]
D = [
    1 -1
    1  1
]
k = size(D, 2)
e = ones(k)

m = Model(solver=CbcSolver())

# Initialize all the variables
@variables m begin
    -10 <= q[1:2, 1:N] <= 10
    -10 <= v[1:2, 1:N] <= 10
    0 <= β[1:k, 1:N] <= 100
    0 <= λ[1:N] <= 100
    0 <= c_n[1:N] <= 100
end

# Set up dynamics and complementarity constraints
for i in 1:(N-1)
    @constraints m begin
        mass * (v[:, i+1] - v[:, i]) .== h * n * c_n[i] .+ h * D * β[:, i] .+ h * mass * g # (5)
        q[:, i + 1] - q[:, i] .== h .* v[:, i + 1] # (6)
        n' * q[:, i + 1] >= 0 # (7)
        λ[i] * e + D' * v[:, i + 1] .>= 0 # (8)
        μ * c_n[i] - e' * β[:, i] >= 0 # (9)
    end
    
    @disjunction m (n' * q[:, i + 1] == 0) (c_n[i] == 0) # (10)
    Dtv = D' * v[:, i + 1]
    for j in 1:k
        @disjunction m ((λ[i] + Dtv[j]) == 0) (β[j, i] == 0) # (11)
    end
    @disjunction m (μ * c_n[i] - e' * β[:, i] == 0) (λ[i] == 0) # (12)
end

# Initial states
@constraints m begin
    q[:, 1] .== [-1, 0.5]
    v[:, 1] .== [2, 0.5]
end

solve(m)
@test getvalue(q[:, end]) ≈ [-0.16892500000000002, 0]
@test getvalue(v[:, end]) ≈ [0, 0]

if Pkg.installed("DrakeVisualizer") !== nothing
    @eval using DrakeVisualizer; 
    @eval using CoordinateTransformations
    DrakeVisualizer.any_open_windows() || DrakeVisualizer.new_window()

    vis = Visualizer()[:block]
    setgeometry!(vis, HyperRectangle(Vec(-0.1, -0.1, 0), Vec(0.2, 0.2, 0.2)))

    for i in 1:length(time)
        settransform!(vis, Translation(getvalue(q[1, i]), 0, getvalue(q[2, i])))
        sleep(h)
    end
end

