using JuMP
using ConditionalJuMP
using Gurobi

struct State{T}
    q::T
    v::T
end

JuMP.getvalue(s::State) = State(getvalue(s.q), getvalue(s.v))

const k = 1000
const Δt = 0.1
const u_max = 10

function update(x::State, u)
    contact_force = ifelse_conditional(@?(x.q <= 0),
        -k * x.q,
        zero(x.q))
    acceleration = u + contact_force
    x_next = State(x.q + Δt * x.v + 0.5 * Δt^2 * acceleration,
                   x.v + Δt * acceleration)
end

function simulate(x0, us)
    xs = [update(x0, us[1])]
    for i in 2:length(us)
        push!(xs, update(xs[end], us[i]))
    end
    xs
end

function run_mpc(x0::State, N=10)
    m = Model(solver=GurobiSolver(OutputFlag=0))
    @variable m -u_max <= u[1:N] <= u_max
    xs = [State(@variable(m, basename="q", lowerbound=-10, upperbound=10),
                @variable(m, basename="v", lowerbound=-10, upperbound=10)) for i in 1:N]
    @constraint m xs[1].q == x0.q
    @constraint m xs[1].v == x0.v
    for i in 2:N
        xi = update(xs[i-1], u[i-1])
        @constraint m xi.q == xs[i].q
        @constraint m xi.v == xs[i].v
    end
    x_f = xs[end]
    @objective(m, Min, 10 * ((x_f.q - 1.0)^2 + x_f.v^2) + 0.01 * sum(u.^2))
    warmstart!(m)
    solve(m)
    getvalue.(xs), getvalue.(u)
end
