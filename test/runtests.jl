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
        m = Model(solver=CbcSolver())
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
        m = Model(solver=CbcSolver())
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
        m = Model(solver=CbcSolver())
        @variable m -5 <= x <= 5
        @variable m -5 <= y[1:2] <= 5
        @implies m x ≤ 0 => y == [3, 3.5]
        @objective m Min x
        @test sum(m.colCat .== :Bin) == 1
        solve(m)
        @test getvalue(x) ≈ lowerbound(x)
        @test getvalue.(y) ≈ [3, 3.5]
    end

    @testset "max" begin
        m = Model(solver=CbcSolver())
        @variable m -5 <= x <= 5
        @variable m -5 <= y[1:2] <= 5
        @implies m x ≥ 0 => y == [1, -1]
        @objective m Max x
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
        setvalue(x, 0.5)
        setup_indicators!(m, true)
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
        setvalue(x, -0.5)
        setup_indicators!(m, true)
        @test sum(m.colCat .== :Bin) == 0
        solve(m)
        @test getvalue.(ys) ≈ [0, 1, -1, 1]
    end
end

function model_latex(m::Model)
    io = IOBuffer()
    show(io, MIME"text/latex"(), m)
    seekstart(io)
    readstring(io)
end

@testset "fixing and unfixing" begin
    m = Model(solver=CbcSolver())
    @variable m -1 <= x <= 1
    @variable m -1 <= y <= 1
    @implies m x ≤ 0 => y == 0.5
    setvalue(x, 0.5)
    @objective(m, Min, x + 0.1y)
    out1 = model_latex(m)

    # Use the value of x as a hint
    setup_indicators!(m)
    @test sum(m.colCat .== :Bin) == 1
    @test model_latex(m) == out1
    solve(m)
    @test getvalue(x) ≈ -1
    @test getvalue(y) ≈ 0.5

    # Now use the current value of x to fix the indicators
    setvalue(x, 0.5)
    setup_indicators!(m, true)
    @test sum(m.colCat .== :Bin) == 0
    solve(m)
    @test getvalue(x) ≈ 0
    @test getvalue(y) ≈ -1

    # Now un-fix the indicators and make sure we get the original
    # model back
    setvalue(x, 0.5)
    setup_indicators!(m)
    @test sum(m.colCat .== :Bin) == 1
    @test model_latex(m) == out1
    solve(m)
    @test getvalue(x) ≈ -1
    @test getvalue(y) ≈ 0.5
end

@testset "disjunctions" begin
    @testset "simple three-way disjunction" begin
        m = Model(solver=CbcSolver())
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
        setup_indicators!(m)
        solve(m)
        @test getvalue(x) ≈ 0
        @test getvalue(y) ≈ -0.5
    end

    @testset "two-way disjunction" begin
        m = Model(solver=CbcSolver())
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
        m = Model(solver=CbcSolver())
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
    @testset "friction with @switch" begin
        include("../examples/friction.jl")
    end

    @testset "block with wall" begin
        if Pkg.installed("Gurobi") !== nothing
            include("../examples/block_with_wall.jl")
            run_mpc(State(1.0, -1.0), 10)
        end
    end
end
