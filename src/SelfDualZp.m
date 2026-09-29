







import "MixZpAdditiveCodes_Core.m": MixZpChangeMatrixZpstoZp;

intrinsic IsSelfOrthogonal(C::MixZpCode) -> BoolElt
    {Returns true if the code C is self-orthogonal under MixZpInnerProduct.}
    
    G := GeneratorMatrix(C`Code);
    k := Nrows(G);
    p := #C`BaseRing;
    MixZpChangeMatrixZpstoZp(~G, p, C`LengthSeq);
    
    for i in [1..k] do
        for j in [i..k] do
            if MixZpInnerProduct(G[i], G[j],  C`LengthSeq) ne 0 then
                return false;
            end if;
        end for;
    end for;
    
    return true;
end intrinsic;

intrinsic IsSelfDual(C::MixZpCode) -> BoolElt
    {Returns true if the code C is self-dual.}
    
    // 1. First check if the code is self-orthogonal
    if not IsSelfOrthogonal(C) then
        return false;
    end if;
    
    // 2. Extract base ring parameters
    lengthSeq := C`LengthSeq;
    type := C`Type;
    s := #C`LengthSeq;
    
    // 3. Compute expected log-cardinality exponent sum(i * alpha_i) / 2
    exp_sum := &+[ i * lengthSeq[i] : i in [1..s] ];
    type_sum := &+[i * type[i] : i in [1..s]];
    
   
    // 4. Verify cardinality condition |C| == p^(exp_sum / 2)
    if type_sum*2 eq exp_sum then
        return true;
    else
        return false ;
    end if;
end intrinsic;






