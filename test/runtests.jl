using ConditionalJuMP
using ConditionalJuMP: switch!,  _getvalue, UnhandledComplementException, hascomplement, getindicator!, disjunction!, isjump, Conditional
using IntervalArithmetic: Interval
using JuMP
using Cbc
using Test
using Random
using Pkg
using Nullables

# Macro hygiene
module MacroHygieneTest
    using ConditionalJuMP: @?
    using Test

    function f(x)
        x + 1
    end

    @testset "macro hygiene" begin
        x = 5
        @test @?(f(x) <= 0) == false
    end
end

@testset "ConditionalJuMP" begin
    @testset "simplification" begin
        test_cases = [
            ("small amount of variables", 100, 20, 1000),
            ("large amount of variables", 10000, 2000, 100),
            ("huge amount of variables", 100000, 20000, 1),
        ]
        for (test_name, num_vars_total, num_vars_in_expr, num_trials) in test_cases
            @testset "$(test_name)" begin
                m = Model()
                Random.seed!(42)
                @variable m q[1:num_vars_total]
                for i in 1:num_trials
                    N = rand(1:num_vars_in_expr)
                    x = randn(N)' * rand(q, N)
                    s1 = copy(x)
                    s2 = copy(x)
                    ConditionalJuMP.simplify_dict!(s1)
                    ConditionalJuMP.simplify_inplace!(s2)
                    @test s1.constant == s2.constant
                    @test length(s1.vars) == length(s2.vars)
                    @test length(s1.coeffs) == length(s2.coeffs)
                    @test length(s1.vars) == length(unique(s1.vars))

                    s1_sorted = sort(collect(zip(s1.vars, s1.coeffs)), by=p -> (p[1].col, p[2]))
                    s2_sorted = sort(collect(zip(s2.vars, s2.coeffs)), by=p -> (p[1].col, p[2]))
                    for (v1, v2) in zip(s1_sorted, s2_sorted)
                        @test v1[1] == v2[1]
                        @test v1[2] ≈ v2[2]
                        # directly testing equality of the two sorted lists is too strict and leads to spurious errors.
                    end
                    for v in s1.vars
                        @test count(x -> x == v, s1.vars) == 1
                    end
                end
            end
        end
    end

    @testset "bounds" begin
        m = Model()
        @variable m 1 <= x <= 3
        e = 2 * x + 1
        @test upperbound(e) == 7
        @test lowerbound(e) == 3
        @test upperbound(e - 2x) == 1
        @test lowerbound(e - 2x) == 1
        @test lowerbound(AffExpr(2)) == 2
        @test upperbound(AffExpr(2)) == 2

        i = interval(e, false)
        @test i == Interval(3, 7)
        @test lowerbound(i) == lowerbound(e)
        @test upperbound(i) == upperbound(e)

        i = interval(5.0)
        @test lowerbound(i) == 5.0
        @test upperbound(i) == 5.0

        i = interval(x)
        @test lowerbound(i) == 1
        @test upperbound(i) == 3
    end

    @testset "simple model" begin
        m = Model()
        @variable m -1 <= x <= 10
        c1 = @?(x <= 0)
        c2 = @?(x >= 0)
        c3 = @?(x + 5 <= 5)
        c4 = @?(x + 1 == 10)

        print(IOBuffer(), c1)
        print(IOBuffer(), c2)
        print(IOBuffer(), c1 & c2)

        @testset "equality" begin
            @test c1 != c2
            @test c2 != c3
            @test c1 == c3
            @test c1 !== c3
        end

        @testset "intersect" begin
            @test (c1 & c3) == c1
            @test length(c1 & c2) == 2
        end

        @testset "complement" begin
            @test !c1 == c2
            @test !c2 == c1
            @test !hascomplement(c4)
            @test_throws UnhandledComplementException !c4
        end

        @testset "hashing" begin
            @test hash(c1) == hash(c3)
            @test hash(c1) != hash(c2)
        end

        @testset "value" begin
            @test isnull(_getvalue(c1))
            @test isnull(_getvalue(c2))
            setvalue(x, -0.1)
            @test get(_getvalue(c1)) == -0.1
            @test get(_getvalue(c2)) == 0.1
        end

        @testset "bounds" begin
            @test lowerbound(x) == -1
            @test upperbound(x) == 10
            @test lowerbound(x + 1) == 0
            @test upperbound(x + 10) == 20
        end

        @testset "indicators" begin
            z1 = getindicator!(m, c1)
            z2 = getindicator!(m, c2)
            z3 = getindicator!(m, c3)
            @test z1 === z3
            @test z1 == !z2
        end

        @testset "isjump" begin
            @test isjump(x)
            @test !isjump(1)
            @test isjump(2x)
            @test isjump(c1)
            @test isjump(c1 & c2)
            @test isjump(c1 => c2)
            @test isjump(c1 => Conditional())
        end
    end

    @testset "disjunction" begin
        m = Model(solver=CbcSolver(logLevel=0))
        @variable m -5 <= x <= 5
        c1 = @?(x >= -4) & @?(x <= -2)
        c2 = @?(x >= 1) & @?(x <= 3)
        @objective m Min x
        disjunction!(m, (c1, c2))
        solve(m)
        @test getvalue(x) ≈ -4
        @objective m Max x
        solve(m)
        @test getvalue(x) ≈ 3
        @constraint m x <= 0
        solve(m)
        @test getvalue(x) ≈ -2
    end

    @testset "implies" begin
        @testset "min" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -5 <= x <= 5
            @variable m -5 <= y <= 5
            @implies m x ≤ 0 => y == 3
            @implies m x ≥ 0 => y == 1
            @objective m Min x

            # test that the two implications are being represented
            # by a single binary variable
            @test sum(m.colCat .== :Bin) == 1
            solve(m)
            @test getvalue(x) ≈ lowerbound(x)
            @test getvalue(y) ≈ 3
        end

        @testset "max" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -5 <= x <= 5
            @variable m -5 <= y <= 5
            @implies m x ≤ 0 => y == 3
            @implies m x ≥ 0 => y == 1
            @objective m Max x

            # test that the two implications are being represented
            # by a single binary variable
            @test sum(m.colCat .== :Bin) == 1
            solve(m)
            @test getvalue(x) ≈ upperbound(x)
            @test getvalue(y) ≈ 1
        end

        @testset "non-disjoint" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -5 <= x <= 5
            @variable m -5 <= y <= 5
            @implies m x ≤ -1 => y == 3
            @implies m x ≥ 1 => y == 1
            @objective m Max x
            @test sum(m.colCat .== :Bin) == 2
            solve(m)
            @test getvalue(x) ≈ upperbound(x)
            @test getvalue(y) ≈ 1
        end
    end

    @testset "vector" begin
        @testset "min" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -5 <= x <= 5
            @variable m -5 <= y[1:2] <= 5
            @implies m x ≤ 0 => y .== [3, 3.5]
            @objective m Min x
            @test sum(m.colCat .== :Bin) == 1
            solve(m)
            @test getvalue(x) ≈ lowerbound(x)
            @test getvalue.(y) ≈ [3, 3.5]
        end

        @testset "max" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -5 <= x <= 5
            @variable m -5 <= y[1:2] <= 5
            @implies m x ≥ 0 => y .== [1, -1]
            @objective m Max x
            @test sum(m.colCat .== :Bin) == 1
            solve(m)
            @test getvalue(x) ≈ upperbound(x)
            @test getvalue.(y) ≈ [1, -1]
        end
    end

    @testset "dynamics" begin
        function update(x)
            @ifelse(x <= 0, 1, -1)
        end

        @testset "mixed integer" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -0.5 <= x <= 0.5

            ys = [x]
            for i in 1:3
                push!(ys, update(ys[end]))
            end

            @objective m Max sum(ys)
            @test sum(m.colCat .== :Bin) == 3
            solve(m)
            @test getvalue.(ys) ≈ [0, 1, -1, 1]
        end

        @testset "seeded positive" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -0.5 <= x <= 0.5

            ys = [x]
            for i in 1:3
                push!(ys, update(ys[end]))
            end

            @objective m Max sum(ys)
            setvalue(x, 0.5)
            warmstart!(m, true)
            @test sum(m.colCat .== :Bin) == 0
            solve(m)
            @test getvalue.(ys) ≈ [0.5, -1, 1, -1]
        end

        @testset "seeded negative" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -0.5 <= x <= 0.5

            ys = [x]
            for i in 1:3
                push!(ys, update(ys[end]))
            end

            @objective m Max sum(ys)
            setvalue(x, -0.5)
            warmstart!(m, true)
            @test sum(m.colCat .== :Bin) == 0
            solve(m)
            @test getvalue.(ys) ≈ [0, 1, -1, 1]
        end

        @testset "vector" begin
            function update2(x)
                @ifelse(x[1] <= 0,
                    [1, 2],
                    [3, 4])
            end

            m = Model(solver=CbcSolver(logLevel=0))
            @variable(m, -10 <= x[1] <= 10)
            y = update2(x)
            @constraint(m, x[1] == -5)
            solve(m)
            @test getvalue(y) ≈ [1, 2]
        end
    end

    function model_latex(m::Model)
        io = IOBuffer()
        show(io, MIME"text/latex"(), m)
        seekstart(io)
        read(io, String)
    end

    @testset "fixing and unfixing" begin
        m = Model(solver=CbcSolver(logLevel=0))
        @variable m -1 <= x <= 1
        @variable m -1 <= y <= 1
        @implies m x ≤ 0 => y == 0.5
        setvalue(x, 0.5)
        @objective(m, Min, x + 0.1y)
        out1 = model_latex(m)

        # Use the value of x as a hint
        warmstart!(m)
        @test sum(m.colCat .== :Bin) == 1
        @test model_latex(m) == out1
        solve(m)
        @test getvalue(x) ≈ -1
        @test getvalue(y) ≈ 0.5

        # Now use the current value of x to fix the indicators
        setvalue(x, 0.5)
        warmstart!(m, true)
        @test sum(m.colCat .== :Bin) == 0
        solve(m)
        @test getvalue(x) ≈ 0
        @test getvalue(y) ≈ -1

        # Now un-fix the indicators and make sure we get the original
        # model back
        setvalue(x, 0.5)
        warmstart!(m)
        @test sum(m.colCat .== :Bin) == 1
        @test model_latex(m) == out1
        solve(m)
        @test getvalue(x) ≈ -1
        @test getvalue(y) ≈ 0.5
    end

    @testset "disjunctions" begin
        @testset "simple three-way disjunction" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -1 <= x <= 1
            @variable m -1 <= y <= 1
            c1 = @?(x <= -0.5)
            c3 = @?(x >= 0.5)
            c2 = !c1 & !c3
            @implies(m,
                c1 => nothing,
                c2 => y == -0.5,
                c3 => nothing)
            @constraint(m, x == 0)
            warmstart!(m)
            solve(m)
            @test getvalue(x) ≈ 0
            @test getvalue(y) ≈ -0.5
        end

        @testset "two-way disjunction" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -1 <= x <= 1
            @variable m -1 <= y <= 1
            c1 = @?(x <= -0.5)
            c2 = @?(x >= 0.5)
            @implies(m,
                c1 => y == 0.1,
                c2 => nothing
                )
            # Test that the two-way disjunction is represented with just one
            # binary variable
            @test sum(m.colCat .== :Bin) == 1
        end

        @testset "missing disjunction" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -1 <= x <= 1
            @variable m -1 <= y <= 1
            c1 = @?(x <= -0.5)
            c3 = @?(x >= 0.5)
            c2 = !c1 & !c3
            @test_throws(
                ConditionalJuMP.UnhandledComplementException,
                @implies(m, c2 => y == -0.5)
                )
        end

        @testset "disjunction with switch" begin
            @testset "case 1" begin
                m = Model(solver=CbcSolver(logLevel=0))
                @variable m -1 <= x <= 1
                c1 = @?(x <= -0.5)
                c3 = @?(x >= 0.5)
                c2 = !c1 & !c3
                y = switch!(m, c1=>0.1, c2=>0.2, c3=>0.3)
                @constraint(m, x == -1)
                warmstart!(m)
                solve(m)
                @test getvalue(x) ≈ -1
                @test getvalue(y) ≈ 0.1
            end
            @testset "case 2" begin
                m = Model(solver=CbcSolver(logLevel=0))
                @variable m -1 <= x <= 1
                c1 = @?(x <= -0.5)
                c3 = @?(x >= 0.5)
                c2 = !c1 & !c3
                y = switch!(m, c1=>0.1, c2=>0.2, c3=>0.3)
                @constraint(m, x == -0)
                warmstart!(m)
                solve(m)
                @test getvalue(x) ≈ 0
                @test getvalue(y) ≈ 0.2
            end
            @testset "case 3" begin
                m = Model(solver=CbcSolver(logLevel=0))
                @variable m -1 <= x <= 1
                c1 = @?(x <= -0.5)
                c3 = @?(x >= 0.5)
                c2 = !c1 & !c3
                y = switch!(m, c1=>0.1, c2=>0.2, c3=>0.3)
                @constraint(m, x == 1)
                warmstart!(m)
                solve(m)
                @test getvalue(x) ≈ 1
                @test getvalue(y) ≈ 0.3
            end
        end

        @testset "disjunction with switch macro" begin
            function f(x)
                @switch(
                    (x <= -0.5) => 0.1,
                    ((x >= -0.5) & (x <= 0.5)) => 0.2,
                    (x >= 0.5) => 0.3
                )
            end

            @test @inferred(f(-1)) == 0.1
            @test @inferred(f(0)) == 0.2
            @test @inferred(f(1)) == 0.3

            @testset "case 1" begin
                m = Model(solver=CbcSolver(logLevel=0))
                @variable m -1 <= x <= 1
                y = f(x)
                @constraint(m, x == -1)
                warmstart!(m)
                solve(m)
                @test getvalue(x) ≈ -1
                @test getvalue(y) ≈ 0.1
            end
            @testset "case 2" begin
                m = Model(solver=CbcSolver(logLevel=0))
                @variable m -1 <= x <= 1
                y = f(x)
                @constraint(m, x == -0)
                warmstart!(m)
                solve(m)
                @test getvalue(x) ≈ 0
                @test getvalue(y) ≈ 0.2
            end
            @testset "case 3" begin
                m = Model(solver=CbcSolver(logLevel=0))
                @variable m -1 <= x <= 1
                y = f(x)
                @constraint(m, x == 1)
                warmstart!(m)
                solve(m)
                @test getvalue(x) ≈ 1
                @test getvalue(y) ≈ 0.3
            end
        end

        @testset "disjunctions with arrays" begin
            function g(x)
                @switch(
                    (x <= -0.5) => [0.1, 1.1],
                    ((x >= -0.5) & (x <= 0.5)) => [0.2, 2.2],
                    (x >= 0.5) => [0.3, 3.3]
                )
            end

            @test @inferred(g(-1)) == [0.1, 1.1]
            @test @inferred(g(0)) == [0.2, 2.2]
            @test @inferred(g(1)) == [0.3, 3.3]

            @testset "case 1" begin
                m = Model(solver=CbcSolver(logLevel=0))
                @variable m -1 <= x <= 1
                y = g(x)
                @constraint(m, x == -1)
                warmstart!(m)
                solve(m)
                @test getvalue(x) ≈ -1
                @test getvalue(y) ≈ [0.1, 1.1]
            end
            @testset "case 2" begin
                m = Model(solver=CbcSolver(logLevel=0))
                @variable m -1 <= x <= 1
                y = g(x)
                @constraint(m, x == -0)
                warmstart!(m)
                solve(m)
                @test getvalue(x) ≈ 0
                @test getvalue(y) ≈ [0.2, 2.2]
            end
            @testset "case 3" begin
                m = Model(solver=CbcSolver(logLevel=0))
                @variable m -1 <= x <= 1
                y = g(x)
                @constraint(m, x == 1)
                warmstart!(m)
                solve(m)
                @test getvalue(x) ≈ 1
                @test getvalue(y) ≈ [0.3, 3.3]
            end
        end

        @testset "simple 1-D example" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable(m, -5 <= x <= 5)
            @disjunction(m, ((x >= -2) & (x <= -1)), ((x >= 1.5) & (x <= 2)))
            # `s` behaves like a poor-man's quadratic objective
            @variable(m, s)
            @constraints m begin
                s >= x
                s >= -x
                s >= 2x - 1
                s >= -2x - 1
            end
            @objective(m, Min, s)
            solve(m)
            @test getvalue(x) ≈ -1

            setvalue(x, 2)
            warmstart!(m, true)
            solve(m)
            @test getvalue(x) ≈ 1.5
        end

        @testset "complementarity" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable(m, -1 <= x <= 1)
            @variable(m, -1 <= y <= 1)
            @disjunction(m, x == 0, y == 0)
            @objective(m, Min, x + 2y)
            solve(m)
            @test getvalue(x) ≈ 0
            @test getvalue(y) ≈ -1

            # Check that we can warmstart even when neither case is precisely satisfied
            setvalue(y, 0.01)
            setvalue(x, -0.5)
            warmstart!(m, true)
            solve(m)
            @test getvalue(x) ≈ -1
            @test getvalue(y) ≈ 0
        end

        @testset "disjunction with one entry" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -1 <= x <= 1
            @disjunction m x >= 0.25
            @objective m Min x
            solve(m)
            @test getvalue(x) ≈ 0.25
        end

        @testset "disjunction with overlapping regions" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -2 <= x[1:2] <= 2
            @disjunction(m, x[2] >= 0.5, x[2] <= -0.5, x[1] <= 1)
            @constraint m x[1] == 0.8
            @constraint m x[2] == 0.6
            @test solve(m) == :Optimal
            @test getvalue(x) ≈ [0.8, 0.6]
        end

        @testset "test that warmstart does not introduce new variables" begin
            m = Model(solver=CbcSolver(logLevel=0))
            @variable m -1 <= x <= 1
            @disjunction m (x == 0.5) (x == -0.5)
            @objective m Min x
            @test length(m.colCat) == 2
            warmstart!(m, false)
            @test length(m.colCat) == 2
            solve(m)
            @test getvalue(x) ≈ -0.5
            warmstart!(m, true)
            @test length(m.colCat) == 2
            solve(m)
            @test getvalue(x) ≈ -0.5
        end
    end

    @testset "examples" begin
        @testset "friction with @switch" begin
            include("../examples/friction.jl")
        end

        @testset "block with wall" begin
            if haskey(Pkg.installed(), "Gurobi")
                include("../examples/block_with_wall.jl")
                run_mpc(State(1.0, -1.0), 10)
            end
        end

        @testset "complementarity" begin
            include("../examples/complementarity.jl")
        end

        @testset "polyhedra" begin
            include("../examples/polyhedra.jl")
        end
    end

    @testset "constant objective" begin
        m = Model(solver=CbcSolver())
        @variable m x >= 0
        @objective m Min x - 1
        ConditionalJuMP.handle_constant_objective!(m)
        @test getobjective(m).aff.constant == 0
        @test sum(m.colCat .== :Cont) == 1
        @test sum(m.colCat .== :Fixed) == 1
        solve(m)
        @test getvalue(x) ≈ 0
    end
end
