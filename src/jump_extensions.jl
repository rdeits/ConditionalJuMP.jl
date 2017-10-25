getmodel(x::JuMP.Variable) = x.m
getmodel(x::JuMP.GenericAffExpr) = x.vars[1].m
getmodel(x) = nothing

nan_to_null(x) = isnan(x) ? Nullable{typeof(x)}() : Nullable{typeof(x)}(x)

"""
Like JuMP.getvalue, but returns a Nullable{T}() for unset variables instead
of throwing a warning
"""
function _getvalue(x::JuMP.GenericAffExpr{T, Variable}) where {T}
    result::Nullable{T} = x.constant
    for i in eachindex(x.coeffs)
        result = result .+ x.coeffs[i] .* _getvalue(x.vars[i])
    end
    result
end

_getvalue(x::Variable) = nan_to_null(JuMP._getValue(x))
_getvalue(x::Number) = nan_to_null(x)

_setvalue(v::Variable, x) = JuMP.setvalue(v, x)
function _setvalue(s::JuMP.GenericAffExpr, x)
    @assert length(s.vars) == 1
    _setvalue(s.vars[1], (x - s.constant) / s.coeffs[1])
end
