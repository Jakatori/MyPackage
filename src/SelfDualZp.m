

intrinsic IsSelfOrthogonal(C::MixZpCode) -> BoolElt
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


intrinsic IsSelfDual(C::MixZpCode) -> BoolElt
    {Returns true if the code C is self-dual.}

    // A self-dual code must first be self-orthogonal
    if not IsSelfOrthogonal(C) then
        return false;
    end if;

    s := #C`LengthSeq;

    // Compute the exponent corresponding to half the
    // logarithm of the size of the ambient space.
    exp_sum := &+[i * C`LengthSeq[i] : i in [1..s]];

    // Compute log_p(|C|) from the type of C.
    type_sum := &+[i * C`Type[i] : i in [1..s]];

    // The ambient-space exponent must be even, and
    // |C| must be the square root of the ambient-space size.
    if not IsZero(exp_sum mod 2) then
        return false;
    else
        return exp_sum div 2 eq type_sum;
    end if;

end intrinsic;
