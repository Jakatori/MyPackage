



intrinsic MixZpInnerProduct(u::ModTupRngElt, v::ModTupRngElt, lengthSeq::SeqEnum[RngIntElt]) -> RngIntElt
    {Computes the mixed Z_p^s inner product for u and v given block lengths lengthSeq = [alpha_1, ..., alpha_s].}
    
    R := BaseRing(Parent(u));
    sizeRing := #R;

    p := PrimeFactors(sizeRing)[1];
    s := Valuation(sizeRing, p);

    require #lengthSeq eq s:
        "lengthSeq must contain one entry for each power of p.";

    require Parent(u) eq Parent(v):
        "Vectors must belong to the same parent.";

    require &and[ell ge 0 : ell in lengthSeq]:
        "Block lengths must be non-negative.";

    require Degree(Parent(u)) eq &+lengthSeq:
        "Vector length does not match sum of lengthSeq.";
    
    sum := R ! 0;
    col_idx := 1;
    
    for i in [1..s] do
        scale := R ! (p^(s - i));
        for k in [1..lengthSeq[i]] do
            sum +:= scale * u[col_idx] * v[col_idx];
            col_idx +:= 1;
        end for;
    end for;
    
    return sum;
end intrinsic;
