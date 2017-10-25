
lowerbound(x::Number) = x
lowerbound(x::AbstractJuMPScalar) = -upperbound(-x)
upperbound(x::Number) = x
upperbound(x::Variable) = JuMP.getupperbound(x)

function simplify(e::JuMP.GenericAffExpr{T, Variable}) where T
    coeffs = Dict{Variable, T}()
    for i in eachindex(e.vars)
        v, c = e.vars[i], e.coeffs[i]
        coeffs[v] = get(coeffs, v, zero(T)) + c
    end
    AffExpr(collect(keys(coeffs)), collect(values(coeffs)), e.constant)
end

function upperbound(e::JuMP.GenericAffExpr{T, Variable}) where {T}
    e2 = simplify(e)
    intervals = [Interval(getlowerbound(v), getupperbound(v)) for v in e2.vars]
    if isempty(intervals)
        ex_bounds = Interval(e2.constant, e2.constant)
    else
        ex_bounds = e2.coeffs' * intervals + e2.constant
    end
    ex_bounds.hi
end
