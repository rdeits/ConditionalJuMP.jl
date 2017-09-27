_conditionalize(ex) = esc(ex)

function _conditionalize(ex::Expr)
    if ex.head == :call 
        if ex.args[1] == GlobalRef(Base, :broadcast)
            Expr(:call, :_all_conditional, Expr(:call, GlobalRef(Base, :broadcast), :_conditional, esc.(ex.args[2:end])...))
        elseif ex.args[1] == :(=>)
            Expr(:call, :(=>), _conditionalize.(ex.args[2:end])...)
        else
            Expr(:call, :_conditional, _conditionalize.(ex.args)...)
        end
    else
        esc(ex)
    end
end

macro ?(ex)
    _conditionalize(expand(ex))
end


macro implies(m, args...)
    Expr(:call, :implies!, esc(m), _conditionalize.(expand.(args))...)
end

macro disjunction(m, args...)
    Expr(:call, :disjunction!, esc(m), Expr(:tuple, _conditionalize.(expand.(args))...))
end

macro switch(args...)
    Expr(:call, :switch, _conditionalize.(expand.(args))...)
end

macro ifelse(c, v1, v2)
    Expr(:call, :ifelse, _conditionalize(expand(c)), v1, v2)
end
