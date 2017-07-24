using ConditionalJuMP
using ConditionalJuMP: switch!
using JuMP
using Cbc
using Base.Test

@testset "bounds" begin
    m = Model()
    @variable m 1 <= x <= 3
    e = 2 * x + 1
    @test upperbound(e) == 7
    @test lowerbound(e) == 3
end

@testset "implies" begin
    @testset "min" begin
        m = Model(solver=CbcSolver())
        @variable m -5 <= x <= 5
        @variable m -5 <= y <= 5
        @implies m x <= 0 y == 3
        @implies m x >= 0 y == 1
        @objective m Min x
        setup_indicators!(m)

        # test that the two implications are being represented
        # by a single binary variable
        @test sum(m.colCat .== :Bin) == 1
        solve(m)
        @test getvalue(x) ≈ lowerbound(x)
        @test getvalue(y) ≈ 3
    end

    @testset "max" begin
        m = Model(solver=CbcSolver())
        @variable m -5 <= x <= 5
        @variable m -5 <= y <= 5
        @implies m x <= 0 y == 3
        @implies m x >= 0 y == 1
        @objective m Max x
        setup_indicators!(m)

        # test that the two implications are being represented
        # by a single binary variable
        @test sum(m.colCat .== :Bin) == 1
        solve(m)
        @test getvalue(x) ≈ upperbound(x)
        @test getvalue(y) ≈ 1
    end

    @testset "non-disjoint" begin
        m = Model(solver=CbcSolver())
        @variable m -5 <= x <= 5
        @variable m -5 <= y <= 5
        @implies m x <= -1 y == 3
        @implies m x >= 1 y == 1
        @objective m Max x
        setup_indicators!(m)
        @test sum(m.colCat .== :Bin) == 2
        solve(m)
        @test getvalue(x) ≈ upperbound(x)
        @test getvalue(y) ≈ 1
    end
end

@testset "vector" begin
    @testset "min" begin
        m = Model(solver=CbcSolver())
        @variable m -5 <= x <= 5
        @variable m -5 <= y[1:2] <= 5
        @implies m x <= 0 y == [3, 3.5]
        @objective m Min x
        setup_indicators!(m)
        @test sum(m.colCat .== :Bin) == 1
        solve(m)
        @test getvalue(x) ≈ lowerbound(x)
        @test getvalue.(y) ≈ [3, 3.5]
    end

    @testset "max" begin
        m = Model(solver=CbcSolver())
        @variable m -5 <= x <= 5
        @variable m -5 <= y[1:2] <= 5
        @implies m x >= 0 y == [1, -1]
        @objective m Max x
        setup_indicators!(m)
        @test sum(m.colCat .== :Bin) == 1
        solve(m)
        @test getvalue(x) ≈ upperbound(x)
        @test getvalue.(y) ≈ [1, -1]
    end
end

@testset "dynamics" begin
    function update(x)
        ifelse(@?(x <= 0), 1, -1)
    end

    @testset "mixed integer" begin
        m = Model(solver=CbcSolver())
        @variable m -0.5 <= x <= 0.5

        ys = [x]
        for i in 1:3
            push!(ys, update(ys[end]))
        end

        @objective m Max sum(ys)
        setup_indicators!(m)
        @test sum(m.colCat .== :Bin) == 3
        solve(m)
        @test getvalue.(ys) ≈ [0, 1, -1, 1]
    end

    @testset "seeded positive" begin
        m = Model(solver=CbcSolver())
        @variable m -0.5 <= x <= 0.5

        ys = [x]
        for i in 1:3
            push!(ys, update(ys[end]))
        end

        @objective m Max sum(ys)
        setup_indicators!(m, x=>0.5)
        @test sum(m.colCat .== :Bin) == 0
        solve(m)
        @test getvalue.(ys) ≈ [0.5, -1, 1, -1]
    end

    @testset "seeded negative" begin
        m = Model(solver=CbcSolver())
        @variable m -0.5 <= x <= 0.5

        ys = [x]
        for i in 1:3
            push!(ys, update(ys[end]))
        end

        @objective m Max sum(ys)
        setup_indicators!(m, x=>-0.5)
        @test sum(m.colCat .== :Bin) == 0
        solve(m)
        @test getvalue.(ys) ≈ [0, 1, -1, 1]
    end
end

@testset "disjunctions" begin
    @testset "simple three-way disjunction" begin
        m = Model(solver=CbcSolver())
        @variable m -1 <= x <= 1
        @variable m -1 <= y <= 1
        c1 = @?(x <= -0.5)
        c3 = @?(x >= 0.5)
        c2 = !c1 & !c3
        @implies(m, c2, y == -0.5)
        @disjunction(m, c1, c2, c3)
        @constraint(m, x == 0)
        setup_indicators!(m)
        solve(m)
        @test getvalue(x) ≈ 0
        @test getvalue(y) ≈ -0.5
    end

    @testset "missing disjunction" begin
        m = Model(solver=CbcSolver())
        @variable m -1 <= x <= 1
        @variable m -1 <= y <= 1
        c1 = @?(x <= -0.5)
        c3 = @?(x >= 0.5)
        c2 = !c1 & !c3
        @implies(m, c2, y == -0.5)
        @constraint(m, x == 0)
        @test_throws ConditionalJuMP.UnhandledComplementException setup_indicators!(m)
    end

    @testset "disjunction with switch" begin
        @testset "case 1" begin
            m = Model(solver=CbcSolver())
            @variable m -1 <= x <= 1
            c1 = @?(x <= -0.5)
            c3 = @?(x >= 0.5)
            c2 = !c1 & !c3
            y = switch!(m, c1=>0.1, c2=>0.2, c3=>0.3)
            @constraint(m, x == -1)
            setup_indicators!(m)
            solve(m)
            @test getvalue(x) ≈ -1
            @test getvalue(y) ≈ 0.1
        end
        @testset "case 2" begin
            m = Model(solver=CbcSolver())
            @variable m -1 <= x <= 1
            c1 = @?(x <= -0.5)
            c3 = @?(x >= 0.5)
            c2 = !c1 & !c3
            y = switch!(m, c1=>0.1, c2=>0.2, c3=>0.3)
            @constraint(m, x == -0)
            setup_indicators!(m)
            solve(m)
            @test getvalue(x) ≈ 0
            @test getvalue(y) ≈ 0.2
        end
        @testset "case 3" begin
            m = Model(solver=CbcSolver())
            @variable m -1 <= x <= 1
            c1 = @?(x <= -0.5)
            c3 = @?(x >= 0.5)
            c2 = !c1 & !c3
            y = switch!(m, c1=>0.1, c2=>0.2, c3=>0.3)
            @constraint(m, x == 1)
            setup_indicators!(m)
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
            m = Model(solver=CbcSolver())
            @variable m -1 <= x <= 1
            y = f(x)
            @constraint(m, x == -1)
            setup_indicators!(m)
            solve(m)
            @test getvalue(x) ≈ -1
            @test getvalue(y) ≈ 0.1
        end
        @testset "case 2" begin
            m = Model(solver=CbcSolver())
            @variable m -1 <= x <= 1
            y = f(x)
            @constraint(m, x == -0)
            setup_indicators!(m)
            solve(m)
            @test getvalue(x) ≈ 0
            @test getvalue(y) ≈ 0.2
        end
        @testset "case 3" begin
            m = Model(solver=CbcSolver())
            @variable m -1 <= x <= 1
            y = f(x)
            @constraint(m, x == 1)
            setup_indicators!(m)
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
            m = Model(solver=CbcSolver())
            @variable m -1 <= x <= 1
            y = g(x)
            @constraint(m, x == -1)
            setup_indicators!(m)
            solve(m)
            @test getvalue(x) ≈ -1
            @test getvalue(y) ≈ [0.1, 1.1]
        end
        @testset "case 2" begin
            m = Model(solver=CbcSolver())
            @variable m -1 <= x <= 1
            y = g(x)
            @constraint(m, x == -0)
            setup_indicators!(m)
            solve(m)
            @test getvalue(x) ≈ 0
            @test getvalue(y) ≈ [0.2, 2.2]
        end
        @testset "case 3" begin
            m = Model(solver=CbcSolver())
            @variable m -1 <= x <= 1
            y = g(x)
            @constraint(m, x == 1)
            setup_indicators!(m)
            solve(m)
            @test getvalue(x) ≈ 1
            @test getvalue(y) ≈ [0.3, 3.3]
        end
    end
end

@testset "examples" begin
    @testset "block with wall" begin
        if Pkg.installed("Gurobi") !== nothing
            include("../examples/block_with_wall.jl")
            run_mpc(State(1.0, -1.0), 10)
        end
    end
end
