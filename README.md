# JuMPIndicators

[![Build Status](https://travis-ci.org/rdeits/JuMPIndicators.jl.svg?branch=master)](https://travis-ci.org/rdeits/JuMPIndicators.jl) [![codecov.io](http://codecov.io/github/rdeits/JuMPIndicators.jl/coverage.svg?branch=master)](http://codecov.io/github/rdeits/JuMPIndicators.jl?branch=master)

This package is built on top of [JuMP](https://github.com/JuliaOpt/JuMP.jl) and provides basic automatic generation of indicator variables, which allow (limited) statements of the form `condition` *implies* `constraint` in convex optimizations. It does so by automatically introducing binary indicator variables as necessary, and by using interval arithmetic to choose an appropriate big-M formulation.

# Usage

## Basic Implications

```julia
using JuMP, Cbc, JuMPIndicators

m = Model(solver=CbcSolver())
@variable(m, -1 <= x <= 1)  # having bounds on all variables is currently a requirement
@variable(m, -1 <= y <= 1)
# Require that y == 0.5 whenever x <= 0
@implies(m, x <= 0, y == 0.5)
@objective(m, Min, 4x + y)

# setup_indicators!() actually adds the appropriate binary variables to the
# model:
setup_indicators!(m)

solve(m)
@assert getvalue(x) ≈ -1
@assert getvalue(y) ≈ 0.5
```

## Fixing the binary values

It can sometimes be useful to write a model with implication constraints, but then choose to solve that model with the implications fixed. For example, we might wish to try solving the above model both for the case that x <= 0 and for the case that x >= 0. To do that, we can pass variable assignments to `setup_indicators()`, which will use those assignments to determine exactly which sets of constraints should be applied. More concretely:

```julia
m = Model(solver=CbcSolver())
@variable(m, -1 <= x <= 1)  # having bounds on all variables is currently a requirement
@variable(m, -1 <= y <= 1)
# Require that y == 0.5 whenever x <= 0
@implies(m, x <= 0, y == 0.5)
@objective(m, Min, 4x + y)

# Set up the indicator variables for the case that x == 1. Note that this does *not*
# fix x to 1 in the optimization. It simply requires that any implications which depend
# on x will be fixed to the set containing x == 1. In this case, that means that x will
# be fixed to be greater than or equal to 0. 
setup_indicators!(m, x => 1)
solve(m)

@assert getvalue(x) ≈ 0
@assert getvalue(y) ≈ -1
```

```julia
m = Model(solver=CbcSolver())
@variable(m, -1 <= x <= 1)  # having bounds on all variables is currently a requirement
@variable(m, -1 <= y <= 1)
# Require that y == 0.5 whenever x <= 0
@implies(m, x <= 0, y == 0.5)
@objective(m, Min, 4x + y)

# Set up the indicator variables for the case that x == -1. Note that this does *not*
# fix x to -1 in the optimization. It simply requires that any implications which depend
# on x will be fixed to the set containing x == -1. In this case, that means that x will
# be fixed to be less than or equal to 0 AND (by the implication above) y will be fixed 
# to be equal to 0.5
setup_indicators!(m, x => -1)
solve(m)

@assert getvalue(x) ≈ -1
@assert getvalue(y) ≈ 0.5
```

## Disjunctions

This package also provides the `@disjunction` macro, which can operate on simple `if` statements to create functions which can be run both on numbers and on optimization variables. For example, let's write a simple update function:

```julia
function update(x)
    if x <= 0
        1
    else
        -1
    end
end
```

This works on numbers:

```julia
julia> update(0.5)
-1
```

but not on variables:

```julia
julia> m = Model();

julia> @variable m x;

julia> y = update(x)
ERROR: MethodError: no method matching isless(::Int64, ::JuMP.Variable)
Closest candidates are:
  isless(::Real, ::AbstractFloat) at operators.jl:97
  isless(::Real, ::ForwardDiff.Dual) at /home/rdeits/.julia/v0.6/ForwardDiff/src/dual.jl:161
  isless(::Real, ::Real) at operators.jl:266
Stacktrace:
 [1] update(::JuMP.Variable) at ./REPL[3]:2
```

But if we decorate the `if` statement with `@disjunction`, then the function will magically just work in both cases:

```julia
function update(x)
    @disjunction if x <= 0
        1
    else
        -1
    end
end
```

```julia
julia> update(0.5)
-1

julia> m = Model();

julia> @variable m x;

julia> y = update(x)
y
```

Using this, we can easily write optimizations over repeated applications of the `update()` function, which is something we might want to do in a model-predictive control application:

```julia
m = Model(solver=CbcSolver())
@variable m -0.5 <= x <= 0.5

ys = [x]
for i in 1:3
    push!(ys, update(ys[end]))
end

@objective m Max sum(ys)

# setup_indicators!() uses the data recorded by the `@disjunction` macro to set
# up the necessary binary variables to enforce the `if` statement.
setup_indicators!(m)

solve(m)
@assert getvalue.(ys) ≈ [0, 1, -1, 1]
```

The optimal solution is `[0, 1, -1, 1]` because our objective is to maximize the sum of the variables in `ys`. If x were `>=` 0, then our update rule would require the solution to look like `[x, -1, 1, -1]`, which, due to the limits on `0.5 <= x <= 0.5` would have a sub-optimal objective value. So the indicator constraints have indeed given us the optimal solution. 

# Implementation Notes

Indicator constraints are currently enforced using a Big-M formulation. This formulation works by transforming the constraint: `z == 1 implies x <= 0` into the constraint:

```
x <= 0 + M * (1 - z)
```

where `z` is restricted to be either 0 or 1. 

If `M` is sufficiently large, then when `z == 0`, `x` is essentially unbounded. But when `z == 1`, the constraint reduces to `x <= 0` as desired. The key to successfully applying this formulation is choosing the right value of `M`. Too small an `M` will restrict `x` even when `z == 0`. Too large a value will create numerical difficulties in the solver. 

JuMPIndicators.jl uses [IntervalArithmetic.jl](https://github.com/JuliaIntervals/IntervalArithmetic.jl) to solve for an appropriate value of `M` automatically. The idea is that if we know the bounds on `x` (from the upper and lower bounds in the JuMP model), we can compute exactly how large M needs to be. Even more complicated expressions like `z == 1 implies (2x + 3y + z - 2 <= 5x)` can be handled automatically because IntervalArithmetic.jl already knows how to propagate intervals through various functions. 

As an example, let's look back at the first model:

```julia
m = Model(solver=CbcSolver())
@variable(m, -1 <= x <= 1)  # having bounds on all variables is currently a requirement
@variable(m, -1 <= y <= 1)
# Require that y == 0.5 whenever x <= 0
@implies(m, x <= 0, y == 0.5)
@objective(m, Min, 4x + y)

# setup_indicators!() actually adds the appropriate binary variables to the
# model:
setup_indicators!(m)
```

The constraints which are generated for the indicator variable `z` are:

```
x + z <= 1
y + 0.5z <= 1
y - 1.5z >= -1
-x - z <= 0
```

so the sufficiently-big values of M are all in the range [0.5, 1.5], which is certainly small enough not to create numerical problems. 
