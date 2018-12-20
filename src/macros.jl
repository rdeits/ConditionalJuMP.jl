_conditionalize(ex) = esc(ex)

is_function_broadcast(ex::Expr) = ex.head == :(.) && !isa(ex.args[2], QuoteNode) && x.args[2].head == :tuple
is_operator_broadcast(ex::Expr) = ex.head == :(call) && isa(ex.args[1], Symbol) && string(ex.args[1])[1] === '.'


function _conditionalize_function_broadcast(ex::Expr)
    Expr(:call, :_all_conditional, Expr(:call, GlobalRef(Base, :broadcast), :_conditional, esc(ex.args[1]), esc.(ex.args[2].args)...))
end

function _conditionalize_operator_broadcast(ex::Expr)
    Expr(:call, :_all_conditional, Expr(:call, GlobalRef(Base, :broadcast), :_conditional, esc(Symbol(string(ex.args[1])[2:end])), esc.(ex.args[2:end])...))
end


function _conditionalize(ex::Expr)
    if is_function_broadcast(ex)
        _conditionalize_function_broadcast(ex)
    elseif is_operator_broadcast(ex)
        _conditionalize_operator_broadcast(ex)
    elseif ex.head == :call
        if ex.args[1] == :(=>)
            Expr(:call, :(=>), _conditionalize.(ex.args[2:end])...)
        else
            Expr(:call, :_conditional, _conditionalize.(ex.args)...)
        end
    else
        esc(ex)
    end
end

eval(:(macro $(Symbol("?"))(ex) _conditionalize(ex) end))

macro implies(m, args...)
    Expr(:call, :implies!, esc(m), _conditionalize.(args)...)
end

macro disjunction(m, args...)
    Expr(:call, :disjunction!, esc(m), Expr(:tuple, _conditionalize.(args)...))
end

macro switch(args...)
    Expr(:call, :switch, _conditionalize.(args)...)
end

macro ifelse(c, v1, v2)
    Expr(:call, :ifelse_conditional, _conditionalize(c), v1, v2)
end
