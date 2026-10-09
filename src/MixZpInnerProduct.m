intrinsic MixZpInnerProduct(
    C::MixZpCode,
    u::ModTupRngElt,
    v::ModTupRngElt
) -> RngIntElt
{
Computes the mixed Z_p^s inner product of u and v using
the block lengths stored in C.
}

require Parent(u) eq Parent(v):
        "Vectors must belong to the same parent.";

require BaseRing(Parent(u)) eq BaseRing(C`Code):
     "Vectors and code must use the same ring.";

require &and[ell ge 0 : ell in C`LengthSeq]:
    "Block lengths must be non-negative.";

    R := BaseRing(Parent(u));
    sizeRing := #R;

    p := PrimeFactors(sizeRing)[1];
    s := Valuation(sizeRing, p);

    require #C`LengthSeq eq s:
        "The code and vector ring have incompatible parameters.";

    require Degree(Parent(u)) eq &+C`LengthSeq:
        "Vector length does not match the sum of the block lengths.";

    sum := R!0;
    col_idx := 1;

    for i in [1..s] do
        scale := R!(p^(s-i));

        for k in [1..C`LengthSeq[i]] do
            sum +:= scale * u[col_idx] * v[col_idx];
            col_idx +:= 1;
        end for;
    end for;

    return sum;
end intrinsic;