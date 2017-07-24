_conditionalize_recursive!(x) = esc(x)

function _conditionalize_recursive!(ex::Expr)
    if ex.head == :call 
        for i in 2:length(ex.args)
            ex.args[i] = _conditionalize_recursive!(ex.args[i])
        end
        if !(ex.args[1] ∈ (:(=>),))
            Expr(:call, :_conditional, ex.args[1], ex.args[2:end]...)
        else
            Expr(:call, ex.args...)
        end
    else
        esc(ex)
    end
end

macro ?(ex)
    _conditionalize_recursive!(ex)
end

macro implies(m, lhs, rhs)
    quote
        implies!($(esc(m)), 
            $(_conditionalize_recursive!(lhs)),
            $(_conditionalize_recursive!(rhs)))
    end
end

macro disjunction(m, args...)
    Expr(:call, :disjunction!, esc(m),
        _conditionalize_recursive!.(args)...)
end

macro switch(args...)
    Expr(:call, :switch, _conditionalize_recursive!.(args)...)
end
