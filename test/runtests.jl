using JuMPIndicators
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
        @implies m -x <= 0 y == 1
        @objective m Min x
        setup_indicators!(m)
        solve(m)
        @test getvalue(x) ≈ lowerbound(x)
        @test getvalue(y) ≈ 3
    end

    @testset "max" begin
        m = Model(solver=CbcSolver())
        @variable m -5 <= x <= 5
        @variable m -5 <= y <= 5
        @implies m x <= 0 y == 3
        @implies m -x <= 0 y == 1
        @objective m Max x
        setup_indicators!(m)
        solve(m)
        @test getvalue(x) ≈ upperbound(x)
        @test getvalue(y) ≈ 1
    end
end

@testset "dynamics" begin
    function update(x)
        @disjunction if x <= 0
            1
        else
            -1
        end
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
        solve(m)
        @test getvalue.(ys) ≈ [0, 1, -1, 1]
    end
end

@testset "examples" begin
    @testset "block with wall" begin
        include("../examples/block_with_wall.jl")
    end
end
