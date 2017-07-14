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
        solve(m)
        @test getvalue(x) ≈ upperbound(x)
        @test getvalue(y) ≈ 1
    end
end
