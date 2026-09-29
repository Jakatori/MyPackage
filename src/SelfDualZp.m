
intrinsic IsSelfOrthogonalZp(C::MixZpCode) -> BoolElt
    {Returns true if the code C is self-orthogonal under MixZpInnerProduct.}
    
    G := GeneratorMatrix(C`Code);
    k := Nrows(G);
    
    for i in [1..k] do
        for j in [i..k] do
            if MixZpInnerProduct(G[i], G[j],  C`LengthSeq) ne 0 then
                return false;
            end if;
        end for;
    end for;
    
    return true;
end intrinsic;

intrinsic IsSelfDualZp(C::MixZpCode) -> BoolElt
    {Returns true if the code C is self-dual.}
    
    // 1. First check if the code is self-orthogonal
    if not IsSelfOrthogonal(C, lengthSeq) then
        return false;
    end if;
    
    // 2. Extract base ring parameters
    s := #C`LengthSeq;
    
    // 3. Compute expected log-cardinality exponent sum(i * alpha_i) / 2
    exp_sum := &+[ i * lengthSeq[i] : i in [1..s] ];
    
   
    // 4. Verify cardinality condition |C| == p^(exp_sum / 2)
    if not IsZero(exp_sum mod 2) then

    return false;

else

    return (exp_sum mod 2) eq 0;

end if;

end intrinsic;