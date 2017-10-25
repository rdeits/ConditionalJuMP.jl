canonicalize(op, args) = op, args
canonicalize(op::typeof(>=), args::Tuple{Vararg{<:Any, 2}}) = (<=, (args[2] - args[1], 0))
canonicalize(op::typeof(<=), args::Tuple{Vararg{<:Any, 2}}) = (<=, (args[1] - args[2], 0))

struct Conditional{Op, Args <: Tuple}
    op::Op
    args::Args

    function Conditional(op, args) where {}
        canonical_op, canonical_args = canonicalize(op, args)
        new{typeof(canonical_op), typeof(canonical_args)}(
            canonical_op, canonical_args)
    end
end

_getvalue(c::Conditional{typeof(<=), <:Narg{2}}) = _getvalue(c.args[1]) .- _getvalue(c.args[2])
_getvalue(c::Conditional{typeof(>=), <:Narg{2}}) = _getvalue(c.args[2]) .- _getvalue(c.args[1])
_getvalue(c::Conditional{typeof(==), <:Narg{2}}) = abs.(_getvalue(c.args[1]) .- _getvalue(c.args[2]))
_getvalue(c::Conditional{typeof(&)}) = maximum(x -> _getvalue.(x), c.args)

Base.show(io::IO, c::Conditional) = print(io, c.op, c.args)

function getmodel(c::Conditional)
    for arg in c.args
        if getmodel(arg) != nothing
            return getmodel(arg)
        end
    end
    error("Could not find JuMP Model in conditional $c")
end

Conditional(::typeof(>=), x, y) = Conditional(<=, (-x, -y))
(&)(c1::Conditional, cs::Conditional...) = Conditional(&, (c1, cs...))

(==)(c1::Conditional{op}, c2::Conditional{op}) where {op} = c1.args == c2.args

# work-around because JuMP doesn't properly define hash()
function _hash(x::JuMP.GenericAffExpr, h::UInt)
    h = hash(x.constant, h)
    for v in x.vars
        h = hash(v, h)
    end
    for c in x.coeffs
        h = hash(c, h)
    end
    h
end

function Base.hash(c::Union{<:Conditional{typeof(<=), <:Narg{2}}, <:Conditional{typeof(==), <:Narg{2}}}, h::UInt)
    h = hash(c.op, h)
    _hash(c.args[1] - c.args[2], h)
end

Base.@pure isjump(x) = false
Base.@pure isjump(args::Tuple) = any(isjump, args)
Base.@pure isjump(arg::Pair) = isjump(arg.first)
Base.@pure isjump(c::Conditional) = isjump(c.args[1])
Base.@pure isjump(x::AbstractJuMPScalar) = true
Base.@pure isjump(x::AbstractArray{<:AbstractJuMPScalar}) = true

function _conditional(op::Op, args...) where {Op <: Union{typeof(<=), typeof(>=), typeof(==), typeof(in)}}
    if isjump(args)
        Conditional(op, args)
    else
        op(args...)
    end
end

_conditional(op, args...) = op(args...)

function _all_conditional(args)
    (&)(args...)
end

struct ComplementNotDefined
end

complement(c::Conditional) = ComplementNotDefined()
complement(c::Conditional{typeof(<=), <:Narg{2}}) = Conditional(<=, (c.args[2], c.args[1]))
complement(c::Conditional{typeof(>=), <:Narg{2}}) = Conditional(<=, (c.args[1], c.args[2]))
(!)(c::Conditional) = complement(c)

