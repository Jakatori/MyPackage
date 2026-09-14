

intrinsic MixZpInnerProduct(u::ModTupRngElt, v::ModTupRngElt, lengthSeq::SeqEnum[RngIntElt]) -> RngIntElt
    {Computes the mixed Z_p^s inner product for u and v given block lengths lengthSeq = [alpha_1, ..., alpha_s].}
    
    R := BaseRing(Parent(u));
    ps := #R; // Modulus p^s
    
    // Determine p and s from ring size
    p := PrimeFactors(ps)[1];
    s := Valuation(ps, p);
    
    total_len := &+lengthSeq;
    require Degree(Parent(u)) eq total_len: "Vector length does not match sum of lengthSeq.";
    
    sum := R ! 0;
    col_idx := 1;
    
    for i in [1..s] do
        scale := R ! (p^(s - i));
        alpha_i := lengthSeq[i];
        for k in [1..alpha_i] do
            sum +:= scale * u[col_idx] * v[col_idx];
            col_idx +:= 1;
        end for;
    end for;
    
    return sum;
end intrinsic;