
@interface ConditionalIfc(self::Conditional) begin
    getmodel()::Model = getmodel(self)
    getviolation()::Nullable{Float64} = _getvalue(self)
    _hash(h::UInt)::UInt = hash(self, h)
end

Base.hash(ci::ConditionalIfc, h::UInt) = ci._hash(h)
