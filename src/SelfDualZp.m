
intrinsic IsSelfOrthogonalZp(C::Code, lengthSeq::SeqEnum[RngIntElt]) -> BoolElt
    {Returns true if the code C is self-orthogonal under MixZpInnerProduct.}
    
    G := GeneratorMatrix(C);
    k := Nrows(G);
    
    for i in [1..k] do
        for j in [i..k] do
            if MixZpInnerProduct(G[i], G[j], lengthSeq) ne 0 then
                return false;
            end if;
        end for;
    end for;
    
    return true;
end intrinsic;

intrinsic IsSelfDualZp(C::Code, lengthSeq::SeqEnum[RngIntElt]) -> BoolElt
    {Returns true if the code C is self-dual.}
    
    // 1. First check if the code is self-orthogonal
    if not IsSelfOrthogonalZp(C, lengthSeq) then
        return false;
    end if;
    
    // 2. Extract base ring parameters
    R := BaseRing(C);
    ps := #R;
    p := PrimeFactors(ps)[1];
    s := Valuation(ps, p);
    
    // 3. Compute expected log-cardinality exponent sum(i * alpha_i) / 2
    exp_sum := &+[ i * lengthSeq[i] : i in [1..s] ];
    
    if exp_sum mod 2 ne 0 then
        return false; // A self-dual code must have an even exponent sum
    end if;
    
    expected_size := p^(exp_sum div 2);
    
    // 4. Verify cardinality condition |C| == p^(exp_sum / 2)
    return #C eq expected_size;
end intrinsic;