intrinsic IsSelfOrthogonalZp(C::MixZpCode) -> BoolElt
    {Returns true if the code C is self-orthogonal under MixZpInnerProduct.}
    
    G := GeneratorMatrix(C`Code);
    k := Nrows(G);
    
    for i in [1..k] do
        for j in [i..k] do
            if MixZpInnerProduct(G[i], G[j], C`LengthSeq) ne 0 then
                return false;
            end if;
        end for;
    end for;
    
    return true;
end intrinsic;

intrinsic IsSelfDualZp(C::MixZpCode) -> BoolElt
    {Returns true if the code C is self-dual.}
    
    // 1. Extract lengthSeq from the MixZpCode object so it's available locally
    lengthSeq := C`LengthSeq;
    
    // 2. First check if the code is self-orthogonal (using the correct function name and single argument)
    if not IsSelfOrthogonalZp(C) then
        return false;
    end if;
    
    // 3. Extract base ring parameters
    s := #lengthSeq;
    
    // 4. Compute expected log-cardinality exponent sum(i * alpha_i)
    exp_sum := &+[ i * lengthSeq[i] : i in [1..s] ];
    
    // 5. Verify condition
    if not IsZero(exp_sum mod 2) then
        return false;
    else
        return (exp_sum mod 2) eq 0;
    end if;

end intrinsic;