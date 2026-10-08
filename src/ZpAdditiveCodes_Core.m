////////////////////////////////////////////////////////////////////////////////
/////////    Copyright 2021-2023 Adrián Torres and Mercè Villanueva     ////////
/////////                                                               ////////
/////////       This program is distributed under the terms of GNU      ////////
/////////               General Public License                          ////////
/////////                                                               ////////
////////////////////////////////////////////////////////////////////////////////

/*******************************************************************************
    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*******************************************************************************/


/*************************************************************/
/*                                                           */
/* Project name: Z/p^s-additive codes in MAGMA               */
/* File name: ZpAdditiveCodes_Core.m                         */
/*                                                           */
/* Comment: Package developed within the CCSG group          */
/*                                                           */
/* Authors: Javier Esmoris, Noam von Rotberg, Adrián         */
/*          Torres-Martín and Mercè Villanueva               */
/*                                                           */
/* Revision version and last date: v1.0   22-06-2018         */
/*                                 v1.1   17-07-2018         */
/*                                 v1.2   23-07-2018         */
/*             Z2sAdditiveCode.m   v1.3   05-05-2019         */
/*                                 v1.4   14-04-2021         */
/*                                 v1.5   28-08-2021         */
/*                                 v1.6   08-02-2023         */
/*                                 v2.0   12-02-2023         */
/*                                 v2.1   12-12-2023         */
/*                                                           */
/*************************************************************/
//Uncomment freeze when package finished
//freeze

intrinsic ZpAdditiveCodes_Core_version() -> SeqEnum
{Return the current version of this package.}

    version := [2, 1];
    return version;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////            CARLET'S GENERALIZED GRAY MAP FUNCTIONS              ////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */
/* Function name: ParyExpansion                                 */
/* Parameters: u                                                */
/* Function description: Given an element of Z/p^s, it returns  */
/*   the p-ary expansion of u. That is, the unique vector over  */
/*   GF(p) [u_0,...,u_{s-1}] such that                          */
/*   u = u_0 * p^0 + u_1 * p^1... + u_{s-1} * p^(s-1).          */
/* Input parameters description:                                */
/*   - u: an element of Z/p^s                                   */
/* Output parameters description:                               */
/*   - A sequence over GF(p) of length s                        */
/*                                                              */
/****************************************************************/
ParyExpansion := function(u)
    sizeRing := #Parent(u);
    p := Factorization(sizeRing)[1][1];
    s := Valuation(sizeRing, p);
    V := VectorSpace(GF(p), s);

    uParyShort := Intseq(Integers()!u, p);
    uPary := uParyShort cat [0^^(s-#uParyShort)];
    return [Integers(p)!ui : ui in uPary];
end function;

/****************************************************************/
/*                                                              */
/* Function name: ParyComposition                               */
/* Parameters: uZp                                              */
/* Function description: Given a sequence [u_0,...,u_{s-1}] over*/
/*   GF(p), it returns u = u_0 * p^0 + ... + u_{s-1} * p^(s-1)  */
/*   as an element of Z/p^s.                                    */
/* Input parameters description:                                */
/*   - uPary: a sequence over GF(p) of length s                 */
/* Output parameters description:                               */
/*   - An element of Z/p^s                                      */
/*                                                              */
/****************************************************************/
ParyComposition := function(uPary)
    p := #Parent(uPary[1]);
    Zps := Integers(p^(#uPary));

    uInteger := [Integers()!x : x in uPary];
    return Zps!Seqint(uInteger, p);
end function;

/****************************************************************/
/*                                                              */
/* Function name: PhiZp_YwithOnes                               */
/* Parameters: u, YwithOnes, W                                  */
/* Function description: It returns the image of u under the    */
/*   Carlet's generalized Gray map, denoted by Phi              */
/* Input parameters description:                                */
/*   - u: an element of Z/p^s                                   */
/*   - YwithOnes: a matrix over GF(p) necessary to compute the  */
/*        Gray map with its last row full of ones               */
/*   - W: the vector space over GF(p) of dimension s            */
/* Output parameters description:                               */
/*   - A vector over GF(p) as the image of u under Phi          */
/*                                                              */
/****************************************************************/
PhiZp_YwithOnes := function(u, YwithOnes, W)
    uPary := ParyExpansion(u);

    // The product of uPary of size 1 x s and YwithOnes of size s x p^(s-1).
    return (W!uPary) * YwithOnes;
end function;

PhiZp := function(u, Y)
    p := #Parent(Y[1][1]);
    sMinus1 := Nrows(Y);
    V := VectorSpace(GF(p), Ncols(Y));
    W := VectorSpace(GF(p), sMinus1);
    uPary := ParyExpansion(u);

    //Partition the p-ary expansion of u in the first elements and the last element
    uParted := Partition(uPary, [sMinus1, 1]);
    firstElements := uParted[1];
    lastElement := uParted[2][1];

    //(u_{s-1},...,u_{s-1}) p^(s-1) times - the first term of the Phi function
    firstTerm := V![lastElement^^(Ncols(Y))];

    //The matrix product - the second term of the Phi function
    secondTerm := (W!firstElements) * Y;

    return firstTerm + secondTerm;
end function;

/****************************************************************/
/*                                                              */
/* Function name: PhiZpInverse_YwithOnes                        */
/* Parameters: uPary, YwithOnes                                 */
/* Function description: It returns the antiimage of uPary      */
/*   under the Carlet's generalized Gray map, denoted by Phi    */
/* Input parameters description:                                */
/*   - uPary: a vector over Zp of length p^(s-1)                */
/*   - YwithOnes: a matrix over Zp necessary to compute the     */
/*        Gray map with its last row full of ones               */
/* Output parameters description:                               */
/*   - An element of Z/p^s                                      */
/*                                                              */
/****************************************************************/
PhiZpInverse_YwithOnes := function(uPary, YwithOnes)
    uExpansion := Eltseq(Solution(YwithOnes, uPary));

    return ParyComposition(uExpansion);
end function;

PhiZpInverse := function(uPary, Y)
    nparyCoordinate := Ncols(uPary);
    p := #Parent(uPary[1]);
    V := VectorSpace(GF(p), nparyCoordinate);

    w := uPary - V![uPary[1]^^nparyCoordinate];
    firstElements := Eltseq(Solution(Y, w));
    lastElement := [uPary[1]];
    uExpansion := firstElements cat lastElement;

    return ParyComposition(uExpansion);
end function;

/****************************************************************/
/*                                                              */
/* Function name: CarletGrayMap                                 */
/* Parameters: p, s                                             */
/* Function description: Given a prime p and an integer s>1,    */
/*   return Carlet's generalized Grap map phi from              */
/*   Z/(p^s)^n to Zp^(p^(s-1)).                                 */
/* Input parameters description:                                */
/*   - p : a prime number                                       */
/*   - s : an integer greater than 1                            */
/* Output parameters description:                               */
/*   - The Carlet's generalized Gray map                        */
/*                                                              */
/* Signature: (<RngIntElt> p, <RngIntElt> s) -> Map             */
/*                                                              */
/****************************************************************/
intrinsic CarletGrayMap(p::RngIntElt, s::RngIntElt) -> Map
{
Given a prime p and an integer s>1, this function returns Carlet's
generalized Grap map phi_s from Z/(p^s)^n to Zp^(p^(s-1)).
}
    require IsPrime(p): "Argument 1 must be a prime number";
    require s ge 1: "Argument 2 must be an integer greater than 0";

    //Domain
    Zps := Integers(p^s);

    if s eq 1 then
        return map< Zps -> Zps | x :-> x, y :-> y >;
    else
        //Codomain
        K := GF(p);
        nparyCoordinate := p^(s-1);
        V := VectorSpace(K, nparyCoordinate);
        //The matrix used in the Gray map
        Y := Transpose(Matrix([x : x in VectorSpace(K, s-1)]));
        YwithOnes := ZeroMatrix(K, s, nparyCoordinate);
        InsertBlock(~YwithOnes, Y, 1, 1);
        InsertBlock(~YwithOnes, Vector(K, [1^^(nparyCoordinate)]), s, 1);
        W := VectorSpace(GF(p), s);

        return map< Zps -> V | x :-> PhiZp_YwithOnes(x, YwithOnes, W),
                               y :-> Zps!PhiZpInverse_YwithOnes(y, YwithOnes) >;
    end if;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: ZpsPhiCodeword                                */
/* Parameters: c, Y                                             */
/* Function description: It returns the image of the vector c   */
/*   over Z/p^s of length n under the Carlet's generalized Gray */
/*   map. The output is a vector over Zp of length (p^(s-1))n.  */
/* Input parameters description:                                */
/*   - c: a vector over Z/p^s of length n                       */
/*   - Y: a matrix over Zp necessary to compute the Gray map    */
/* Output parameters description:                               */
/*   - A vector over Zp of length (p^(s-1))n                    */
/*                                                              */
/****************************************************************/
ZpsPhiCodeword := function(c, Y)
    return &cat[Eltseq(PhiZp(u, Y)) : u in Eltseq(c)];
end function;

/****************************************************************/
/*                                                              */
/* Function name: ZpsPhiInverseCodeword                         */
/* Parameters: cpary, Y, nparyCoordinate, n, V                  */
/* Function description: It returns the antiimage of the vector */
/*   cpary under the Carlet's generalized Gray map. If the      */
/*   length of cpary is p^(s-1)*n for some integer n, then      */
/*   the output is a vector of Zps^n.                           */
/* Input parameters description:                                */
/*   - cpary: a vector over Zp of length (p^(s-1))n             */
/*   - Y: a matrix over Zp necessary to compute the Gray map    */
/*   - nparyCoordinate: number of Zp coordinates p^(s-1)        */
/*   - n: length of the output vector                           */
/*   - V: vector space over Zp of length nparyCoordinate        */
/* Output parameters description:                               */
/*   - A vector of Zps^n (codeword)                             */
/*                                                              */
/****************************************************************/
ZpsPhiInverseCodeword := function(cpary, Y, nparyCoordinate, n, V)
    cParted := Partition(Eltseq(cpary), [nparyCoordinate^^n]);
    return &cat[[PhiZpInverse(V!i, Y)] : i in cParted];
end function;

/****************************************************************/
/*                                                              */
/* Function name: IsLinearCodeOverZps                           */
/* Parameters:  C                                               */
/* Function description: Given a code C over a ring,            */
/*   this function returns whether the ring is Z/(p^s) and in   */
/*   this case it also returns the integers p and s.            */
/* Input parameters description:                                */
/*   - C : a code over a ring                                   */
/* Output parameters description:                               */
/*   - true if and only if the ring is Z/p^s                    */
/*   - the integer p if the code is over Z/p^s, and 0 otherwise */
/*   - the integer s if the code is over Z/p^s, and 0 otherwise */
/*                                                              */
/****************************************************************/
IsLinearCodeOverZps := function(C)
    alphabet := Alphabet(C);
    if Type(alphabet) eq RngIntRes then
        sizeRing := #alphabet;
        p := Factorization(sizeRing)[1][1];
        s, b := Valuation(sizeRing, p);
        if b eq 1 then
            return true, p, s;
        else
            return false, 0, 0;
        end if;
    else
        return false, 0, 0;
    end if;
end function;

/****************************************************************/
/*                                                              */
/* Function name: IsMatrixOverZps                               */
/* Parameters:  G                                               */
/* Function description: Given a matrix over a ring,            */
/*   this function returns whether the ring is Z/(p^s) and in   */
/*   this case it also returns the integers p and s.            */
/* Input parameters description:                                */
/*   - G : a matrix over a ring                                 */
/* Output parameters description:                               */
/*   - true if and only if the ring is Z/p^s                    */
/*   - the integer p if the code is over Z/p^s, and 0 otherwise */
/*   - the integer s if the code is over Z/p^s, and 0 otherwise */
/*                                                              */
/****************************************************************/
IsMatrixOverZps := function(G)
    ring := BaseRing(G);
    if Type(ring) eq RngIntRes then
        sizeRing := #ring;
        p := Factorization(sizeRing)[1][1];
        s, b := Valuation(sizeRing, p);
        if b eq 1 then
            return true, p, s;
        else
            return false, 0, 0;
        end if;
    else
        return false, 0, 0;
    end if;
end function;

/****************************************************************/
/*                                                              */
/* Function name: CarletGrayMap                                 */
/* Parameters:  C                                               */
/* Function description: Given a code C over Z/p^s of length n, */
/*   this function returns the Carlet's generalized Gray map    */
/*   for C. This is the map phi from C to Zp^(n*p^(s-1)).       */
/* Input parameters description:                                */
/*   - C : a linear code over Z/p^s of length n                 */
/* Output parameters description:                               */
/*   - The Gray map from C to Zp^(n*p^(s-1))                    */
/*                                                              */
/* Signature: (<CodeLinRng> C) -> Map                           */
/*                                                              */
/****************************************************************/
intrinsic CarletGrayMap(C::CodeLinRng) -> Map
{
Given a linear code C over Z/p^s of length n, this function returns Carlet's
generalized Gray map for C. This is the map phi_s from C to Zp^(n*p^(s-1)).

If the linear code C is over Z4, function CarletGrayMap(C) coincides with
function GrayMap(C), which works only for linear codes over Z4.
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 1): "The code C must be over Z/p^s with s>0";

    //The matrix used in the Gray Map
    Y := Transpose(Matrix([x : x in VectorSpace(GF(p), s-1)]));

    //Codomain
    n := Length(C);
    nparyCoordinate := Ncols(Y);
    V := VectorSpace(GF(p), nparyCoordinate);
    Vn := VectorSpace(GF(p), n*nparyCoordinate);

    return map< C -> Vn | c :-> ZpsPhiCodeword(c, Y),
                y :-> C!ZpsPhiInverseCodeword(y, Y, nparyCoordinate, n, V) >;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: CarletGrayMapImage                            */
/* Parameters:  C                                               */
/* Function description: Given a code C over Z/p^s of length n, */
/*   this function returns the image of C under the Carlet's    */
/*   generalized Gray map as a sequence of vectors in           */
/*   GF(p)^(n*p^(s-1)). As the resulting image may not be a     */
/*   linear code over GF(p), a sequence of vectors is returned  */
/*   rather than a code.                                        */
/* Input parameters description:                                */
/*   - C : a linear code over Z/p^s of length n                 */
/* Output parameters description:                               */
/*   - A sequence of vectors of GF(p)^(n*p^(s-1))               */
/*                                                              */
/* Signature: (<CodeLinRng> C) -> [ModTupFldElt]                */
/*                                                              */
/****************************************************************/
intrinsic CarletGrayMapImage(C::CodeLinRng) -> SeqEnum //[ModTupFldElt]
{
Given a code C over Z/p^s of length n, this function returns the image of C under
Carlet's generalized Gray map as a sequence of vectors in GF(p)^(n*p^(s-1)).
As the resulting image may not be a linear code over GF(p), a sequence of vectors
is returned rather than a code.

If the linear code C is over Z4, function CarletGrayMapImage(C) coincides
with GrayMapImage(C), which works only for linear codes over Z4.
}
    mapGray := CarletGrayMap(C);

    return [mapGray(c) : c in C];

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: ZpsPhiInformationSet                          */
/* Parameters:  p, s                                            */
/* Function description: Given a prime p and an integer s>0,    */
/*   return the sequence of coordinate positions Ls = [1, p^0+1,*/
/*   p^1+1,...,p^(s-2)+1], which is an information set for the  */
/*   Carlet's Gray map image of Z/p^s                           */
/* Input parameters description:                                */
/*   - p : A prime number                                       */
/*   - s : A positive integer                                   */
/* Output parameters description:                               */
/*   - A sequence of coordinate positions                       */
/*                                                              */
/* Function developed by Adrián Torres                          */
/*                                                              */
/****************************************************************/
ZpsPhiInformationSet := func< p, s | [1] cat [p^i + 1 : i in [0..(s-2)]] >;

/****************************************************************/
/*                                                              */
/* Function name: ZpsPhiInfo                                    */
/* Parameters:  u, T                                            */
/* Function description: Given an information vector over Z/p^s */
/*   for a linear code over Z/p^s of type T=[t1,t2,...,ts], so  */
/*   a vector of lenght t1+t2+...+ts, return the corresponding  */
/*   information vector over GF(p) after applying the Gray map. */
/* Input parameters description:                                */
/*   - v : An information vector over Z/p^s                     */
/*   - T : A sequence containing the type [t1,...,ts]           */
/* Output parameters description:                               */
/*   - A vector over GF(p)                                      */
/*                                                              */
/* Function developed by Adrián Torres                          */
/*                                                              */
/****************************************************************/
ZpsPhiInfo := function(u, T)
    sizeRing := #Parent(u[1]);
    // The size of the ring is always p^s, since the ring is Z/p^s
    ps := Factorization(sizeRing)[1];
    p := ps[1];
    s := ps[2];

    w := [];
    pos := 1;
    for i in [1..s] do
        Y := Transpose(Matrix([x : x in VectorSpace(GF(p), s-i)]));
        Y := VerticalJoin(Y, Vector(GF(p), [1^^(p^(s-i))]));
        Yrestricted := Submatrix(Y, [1..Nrows(Y)],
                                    ZpsPhiInformationSet(p, s-i+1));
        V := VectorSpace(GF(p), s-i+1);
        for j in [1..T[i]] do
            uPary := V!ParyExpansion(u[pos])[1..(s-i+1)];
            w := w cat Eltseq(uPary * Yrestricted);
            pos +:= 1;
        end for;
    end for;

    return w;
end function;

/****************************************************************/
/*                                                              */
/* Function name: ZpsPhiInverseInfo                             */
/* Parameters:  v, T                                            */
/* Function description: Given an information vector v in the   */
/*   form GF(p)^(s*t1+(s-1)*t2,...,ts), returns the antiimage of*/
/*   the generalized Carlet Gray map. That is, for each set of  */
/*   coordinates we use a Gray map with different dimensions.   */
/*   For instance, for the first s*t1 coordinates we compute an */
/*   antiimage in Z_ps^t1, for the next (s-1)*t2 the antiimage  */
/*   is in Z_p(s-1)^(t2) and so on.                             */
/* Input parameters description:                                */
/*   - v : An information vector over GF(p)                     */
/*   - T : A sequence containing the type [t1,...,ts]           */
/* Output parameters description:                               */
/*   - A vector of (Z/p^s)^t1 x (Z/p^(s-1))^t2 x ··· x Zp^ts    */
/*     as an element of (Z/p^s)^(t1+···+ts)                     */
/*                                                              */
/* Function developed by Adrián Torres                          */
/*                                                              */
/****************************************************************/
ZpsPhiInverseInfo := function(v, T)
    s := #T;
    p := #Parent(v[1]);
    Zps := Integers(p^s);

    w := [];
    pos := 1;
    for i in [1..s] do
        Y := Transpose(Matrix([x : x in VectorSpace(GF(p), s-i)]));
        Y := VerticalJoin(Y, Vector(GF(p), [1^^(p^(s-i))]));
        Yrestricted := Submatrix(Y, [1..Nrows(Y)],
                                    ZpsPhiInformationSet(p, s-i+1));
        V := VectorSpace(GF(p), s-i+1);
        for j in [1..T[i]] do
            vExpansion := Eltseq(Solution(Yrestricted, V!Eltseq(v)[pos..(pos+s-i)]));
            w := w cat [Zps!ParyComposition(vExpansion)]; // Rethink this
            pos := pos+1+s-i;
        end for;
    end for;

    return w;
end function;

/****************************************************************/
/*                                                              */
/* Function name: DivideByP                                     */
/* Parameters:  u, p, T                                         */
/* Function description: Given an element u of p^t(Z/p^s) return*/
/*   the corresponding element of the isomorphic group Z/p^(s-t)*/
/*   dividing u by p^t, for t in [0..s-1]. The sequence T=[t1,  */
/*   ,...,ts] indicates that the first t1 coordinates are over  */
/*   Z/p^s, the next t2 over p(Z/p^(s-1)), ... , and the last ts*/
/*   over p^(s-1)Zp, and they are divided by 1, p, ..., p^(s-1),*/
/*   respectively.                                              */
/* Input parameters description:                                */
/*   - u : A vector of (Z/p^s)^(t1+...+ts)                      */
/*   - p : A prime number                                       */
/*   - T : A sequence with nonnegative integers t1,...,ts       */
/* Output parameters description:                               */
/*   - A vector of (Z/p^s)^t1 x (Z/p^(s-1))^t2 x ··· x Zp^ts    */
/*     as an element of (Z/p^s)^(t1+···+ts)                     */
/*                                                              */
/* Function developed by Adrián Torres                          */
/*                                                              */
/****************************************************************/
DivideByP := function(u, p, T)
    pos := 1;
    for i in [1..#T] do
        divisor := p^(i-1);
        for j in [1..T[i]] do
            u[pos] := u[pos] div divisor;
            pos +:= 1;
        end for;
    end for;

    return u;
end function;

/****************************************************************/
/*                                                              */
/* Function name: MultiplyByP                                   */
/* Parameters:  u, p, T                                         */
/* Function description: Given an element u of Z/p^(s-t) return */
/*   the corresponding element of the isomorphic group p^t(Z/p^s)*/
/*   multiplying u by p^t. The sequence T=[t1,...,ts] indicates */
/*   that the first t1 coordinates are over Z/p^s, the next t2  */
/*   over (Z/p^(s-1)), ... , and the last ts over Zp, and they  */
/*   are multiplied by 1, p, ..., p^(s-1), respectively.        */
/* Input parameters description:                                */
/*   - u : A vector of (Z/p^s)^t1 x (Z/p^(s-1))^t2 x ··· x Zp^ts*/
/*     as an element of (Z/p^s)^(t1+···+ts)                     */
/*   - p : A prime number                                       */
/*   - T : A sequence with nonnegative integers t1,...,ts       */
/* Output parameters description:                               */
/*   - A vector of (Z/p^s)^(t1+...+ts)                          */
/*                                                              */
/* Function developed by Adrián Torres                          */
/*                                                              */
/****************************************************************/
MultiplyByP := function(u, p, T)
    pos := 1;
    for i in [1..#T] do
        mult := p^(i-1);
        for j in [1..T[i]] do
            u[pos] := u[pos] * mult;
            pos +:= 1;
        end for;
    end for;

    return u;
end function;

/****************************************************************/
/*                                                              */
/* Function name: CarletGrayMap                                 */
/* Parameters:  p, T                                            */
/* Function description: Given a prime p and a sequence T=[t1,  */
/*   ...,ts] of s nonnegative integers, return a map from       */
/*   the Zp^s-submodule of Z/p^s^(t1+...+ts) isomorphic to      */
/*   (Z/p^s)^t1 x ... x Zp^ts to the space Zp^k, where          */
/*   k=t1*p^(s-1) + t2*p^(s-2) + ... + ts. In the first t1      */
/*   coordinates, Carlet's generalized Gray map phi_s from      */
/*   Z/p^s to Zp^(p^(s-1)) is considered; in the next t2,       */
/*   Carlet's generalized Gray map phi_(s-1) from Z/p^(s-1) to  */
/*   Zp^(p^(s-2)); and so on, until the last ts coordinates,    */
/*   where the identity map phi_1 form Zp to Zp is considered.  */
/*   The map is also provided with an inverse function, since   */
/*   it is bijective.                                           */
/* Input parameters description:                                */
/*   - p : a prime number                                       */
/*   - s : an integer greater than 1                            */
/* Output parameters description:                               */
/*   - A map phi, which is Carlet's Gray map from the           */
/*     information space of a linear code C over Z/p^s to the   */
/*     information space of phi_s(C)                            */
/*                                                              */
/* Function developed by Adrián Torres                          */
/*                                                              */
/* Signature: (<RngIntElt> p, <SeqEnum> T) -> Map               */
/*                                                              */
/****************************************************************/
intrinsic CarletGrayMap(p::RngIntElt, T::SeqEnum[RngIntElt]) -> Map
{
Given a prime p and a sequence T=[t1,...,ts] of s nonnegative integers, this
function returns a map from the (Z/p^s)-submodule of (Z/p^s)^(t1+...+ts)
isomorphic to (Z/p^s)^t1 x ... x Zp^ts to the space Zp^k, where k=t1*p^(s-1)
+ t2*p^(s-2) + ... + ts. In the first t1 coordinates, Carlet's generalized
Gray map phi_s from Z/p^s to Zp^(p^(s-1)) is considered; in the next t2,
Carlet's generalized Gray map phi_(s-1) from Z/p^(s-1) to Zp^(p^(s-2)); and
so on, until the last ts coordinates, where the identity map phi_1 form Zp to
Zp is considered. The map is also provided with an inverse function, since
it is bijective.

Note that this map coincides with Carlet's generalized Gray map from the
information space of a linear code C over Z/p^s of type (n; t1,...,ts)
(as a Z/p^s-submodule) to the information space of phi_s(C).
}
    require IsPrime(p) : "Argument 1 must be a prime number";
    require not(IsEmpty(T)): "Argument 2 can not be an empty sequence";
    require Min(T) ge 0: "Argument 2 must be a sequence of nonnegative integers";

    s := #T;
    Zps := Integers(p^s);

    if &+T eq 0 then
        R := RSpace(Zps, 0);
        V := VectorSpace(GF(p), 0);
        return map <R -> V | r :-> V!0, v :-> R!0>;
    end if;

    diagonal := [p^(i-1) : j in [1..T[i]], i in [1..s]];
    R := RSpace(LinearCode(DiagonalMatrix(Zps, diagonal)));
    V := VectorSpace(GF(p), &+[T[i]*(s-i+1) : i in [1..#T]]);
    return map< R -> V | r :-> V!ZpsPhiInfo(DivideByP(r, p, T), T),
                         v :-> R!MultiplyByP(ZpsPhiInverseInfo(v, T), p, T) >;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: OTimesProduct                                 */
/* Parameters: p, u, v                                          */
/* Function description: Given two elements of Z/p^s, u and v,  */
/*   this function returns the element of Z/p^s with p-ary      */
/*   expansion [w_0,...,w_(s-1)], where w_i=1 if u_i+v_i>=p and */
/*   0 otherwise, and [u_0,...,u_(s-1)] and [v_0,...,v_(s-1)]   */
/*   are the p-ary expansions of u and v, respectively.         */
/* Input parameters description:                                */
/*   - p: a prime number                                        */
/*   - u: an element of Z/p^s                                   */
/*   - v: an element of Z/p^s                                   */
/* Output parameters description:                               */
/*   - An element of Z/p^s                                      */
/*                                                              */
/****************************************************************/
OTimesProduct := function(p, u, v)
    Zp := Integers(p);
    uExpansion := ParyExpansion(u);
    vExpansion := ParyExpansion(v);

    wExpansion := [Integers()!uExpansion[i] + Integers()!vExpansion[i] ge p
                   select Zp!1 else Zp!0 : i in [1..#uExpansion]];

    return ParyComposition(wExpansion);
end function;

/****************************************************************/
/*                                                              */
/* Function name: OTimesVectorProduct                           */
/* Parameters: p, u, v                                          */
/* Function description: Given a prime and two vectors of the   */
/*   same dimension over Z/p^s, apply OTimesProduct             */
/*   componentwise.                                             */
/* Input parameters description:                                */
/*   - p: a prime number                                        */
/*   - u: a  vector over Z/p^s                                  */
/*   - v: a  vector over Z/p^s (of same dimension as u)         */
/* Output parameters description:                               */
/*   - A vector over Z/p^s                                      */
/*                                                              */
/****************************************************************/
OTimesVectorProduct := function(p, u, v)
    n := OverDimension(u);
    return RSpace(BaseRing(u), n)![OTimesProduct(p, u[i], v[i]) : i in [1..n]];
end function;

/****************************************************************/
/*                                                              */
/* Function name: HasLinearCarletGrayMapImage                   */
/* Parameters:  C                                               */
/* Function description: Given a linear code C over Z/p^s of    */
/*   length n, this function returns true if and only if the    */
/*   image of C under Carlet's generalized Gray map is a linear */
/*   code over Zp. If so, the function also returns the image   */
/*   C_p as a linear code over Zp, together with the bijection  */
/*   phi_s: C -> C_p.                                           */
/* Input parameters description:                                */
/*   - C : a linear code over Z/p^s of length n                 */
/* Output parameters description:                               */
/*   - true if and only if the image is a linear code over Zp.  */
/*     If return true, then                                     */
/*   - A linear code over Zp, 0 otherwise                       */
/*   - A map from C to B, 0 otherwise                           */
/*                                                              */
/* Signature: (<CodeLinRng> C) -> BoolElt, CodeLinRng, Map      */
/*                                                              */
/****************************************************************/
intrinsic HasLinearCarletGrayMapImage(C::CodeLinRng : AlgMethod := "StarProduct")
                                                    -> BoolElt, CodeLinRng, Map
{
Given a linear code C over Z/p^s of length n, this function returns true if
and only if the image of C under Carlet's generalized Gray map is a linear code
over Zp. If so, the function also returns the image C_p as a linear code over Zp,
together with the bijection phi_s: C -> C_p.

The user can specify the method to be used by setting the parameter AlgMethod to
"BruteForce", "StarProduct" or "StarProductMemory". The first one is based on
computing the span of the Gray map image of C, and the other two on Theorem 4.13
given in the below reference, without considering some of the codewords of order p.
"StarProductMemory" method does more computations than "StarProduct", but it
does not need to store any set of codewords. By default, AlgMethod is set to
"StarProduct". However, sometimes the brute force method can be faster, for
example, when the image of C under Carlet’s Gray map gives a linear code over
Fp, that is, when almost all pairs of codewords need to be checked in the
default method. In cases where there is not enough memory to perform the default
method, the option "StarProductMemory" can be used.

If the linear code C is over Z4, HasLinearCarletGrayMapImage(C) coincides with
function HasLinearGrayMapImage(C), which works only for linear codes over Z4.

Reference: Tapia-Recillas, H., Vega, G.: On Z2k-linear and quaternary codes.
SIAM J. Discrete Math. 17(1), pp. 103–113, 2003.
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>0";
    require Type(AlgMethod) eq MonStgElt:
                         "The optional parameter AlgMethod must be a string";

    // if s=1, the Gray map image coincides with C, so it is linear
    if s eq 1 then
        return true, C, map<C -> C | v :-> v, w :-> w>;
    end if;

    np := Length(C)*p^(s-1);

    case AlgMethod :
        // Brute force version, which is perhaps faster when the Gray map image is linear
        when "BruteForce" :
            B := CarletGrayMapImage(C);
            V := VectorSpace(GF(p), np);
            S := sub< V | B >;

            if #B eq p^Dimension(S) then
                Cp := LinearCode(S);
                mapGray := CarletGrayMap(C);
                bijection := map<C -> Cp  | v :-> mapGray(v), w :-> w @@ mapGray >;
                return true, Cp, bijection;
            else
                return false, 0, 0;
            end if;

        // New version StarProduct, which represents an alternative method when there
        // is a "failed memory request" while using the default version "StarProduct"
        when "StarProductMemory" :
            G := ZpMinRowsGeneratorMatrix(C);
            type := ZpType(C);
            Gs := RowSubmatrix(G, &+type-type[s]);
            Cs := LinearCode(Gs);
            for c1 in Cs do
                for c2 in Cs do
                    if not p*OTimesVectorProduct(p, c1, c2) in C
                        then return false, 0, 0;
                    end if;
                end for;
            end for;

            Cp := LinearCode<GF(p), np | CarletGrayMapImage(C)>;
            mapGray := CarletGrayMap(C);
            bijection := map<C -> Cp  | v :-> mapGray(v), w :-> w @@ mapGray >;
            return true, Cp, bijection;

        // Default version "StarProduct"
        // It seems to be more suitable when the Gray map image is nonlinear
        else :
            G := ZpMinRowsGeneratorMatrix(C);
            type := ZpType(C);
            Gs := RowSubmatrix(G, &+type-type[s]);
            Cs := LinearCode(Gs);
            codewords := Setseq(Set(Cs));
            for i in [1..#codewords] do
                for j in [i..#codewords] do
                    if not p*OTimesVectorProduct(p, codewords[i], codewords[j]) in C
                        then return false, 0, 0;
                    end if;
                end for;
            end for;

            Cp := LinearCode<GF(p), np | CarletGrayMapImage(C)>;
            mapGray := CarletGrayMap(C);
            bijection := map<C -> Cp  | v :-> mapGray(v), w :-> w @@ mapGray >;
            return true, Cp, bijection;

    end case;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////                  GENERALIZED GRAY MAP FUNCTIONS                 ////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */
/* Function name: BinaryMatrixToOrdinaryMatrix                  */
/* Parameters: M                                                */
/* Function description: Given a binary matrix M of order n,    */
/*   return the matrix resulting from swapping 1's for -1's and */
/*   0's for +1's.                                              */
/* Input parameters description:                                */
/*   - M: A binary matrix                                       */
/* Output parameters description:                               */
/*   - The corresponding matrix of +1's and -1's                */
/*   - A bool that indicates if the given matrix M is binary    */
/*                                                              */
/****************************************************************/
BinaryMatrixToOrdinaryMatrix := function(M)
    n := Nrows(M);
    Mordinary := Matrix(Integers(), n, n, []);
    for i in [1..n] do
        for j in [1..n] do
            if M[i][j] eq 1 then
                Mordinary[i][j] := -1;
            else
                Mordinary[i][j] := 1;
            end if;
        end for;
    end for;

    return Mordinary;
end function;

/****************************************************************/
/*                                                              */
/* Function name: OrdinaryMatrixToBinaryMatrix                  */
/* Parameters: M                                                */
/* Function description: Given a matrix M of 1's and -1's of    */
/*   order n, return the matrix resulting from swapping 1's     */
/*   for 0's and -1's for 1's.                                  */
/* Input parameters description:                                */
/*   - M: A matrix of 1's and -1's                              */
/* Output parameters description:                               */
/*   - The corresponding binary matrix                          */
/*   - A bool that indicates if the given matrix M is a matrix  */
/*     of +1's and -1's                                         */
/*                                                              */
/****************************************************************/
OrdinaryMatrixToBinaryMatrix := function(M)
    n := Nrows(M);
    Mbinary := Matrix(GF(2), n, n, []);
    for i in [1..n] do
        for j in [1..n] do
            if M[i][j] eq -1 then
                Mbinary[i][j] := 1;
            elif M[i][j] eq 1 then
                Mbinary[i][j] := 0;
            else
                return M, false;
            end if;
        end for;
    end for;

    return Mbinary, true;
end function;

/****************************************************************/
/*                                                              */
/* Function name: IsHadamardMatrix                              */
/* Parameters: H                                                */
/* Function description: Returns true if and only if H is a     */
/*   generalized Hadamard matrix over Fq or an ordinary         */
/*   Hadamard matrix of +1's and -1's. If H is an ordinary      */
/*   Hadamard matrix, the return is the same as that of function*/
/*   IsHadamard(H).                                             */
/* Input parameters description:                                */
/*   - H: A matrix                                              */
/* Output parameters description:                               */
/*   - true if the matrix is a generalized Hadamard matrix,     */
/*     and false otherwise                                      */
/*                                                              */
/* Signature: (<AlgMatElt> H) -> BoolElt                        */
/*                                                              */
/****************************************************************/
intrinsic IsHadamardMatrix(H::AlgMatElt) -> BoolElt
{
Returns true if and only if H is a generalized Hadamard matrix over Fq or an
ordinary Hadamard matrix of +1's and -1's. If H is an ordinary Hadamard matrix,
the return is the same as that of function IsHadamard(H).
}
    F := BaseRing(H);

    // if H is over Z, it is checked whether H is an ordinary matrix
    if Type(F) eq RngInt then
        return IsHadamard(H), H;

    // if H is over a finite field or Zp with p prime, it is checked
    // whether H is a generalized Hadamard matrix over this field or ring
    elif (Type(F) eq FldFin) or ((Type(F) eq RngIntRes) and IsPrime(#F)) then
        if (#F eq 2) then
            Hordinary := BinaryMatrixToOrdinaryMatrix(H);
            return IsHadamard(Hordinary), Hordinary;

        else
            n := Nrows(H);
            q := #F;
            if IsDivisibleBy(n, q) then
                L := n/q;
                elementsF := [s : s in F];

                for i in [1..n] do
                    for j in [(i+1)..n] do
                        multiplicityF := [0^^q];
                        for k in [1..n] do
                            d := Position(elementsF, H[i][k] - H[j][k]);
                            multiplicityF[d] := multiplicityF[d] + 1;
                        end for;
                        for k in [1..q] do
                            if not multiplicityF[k] eq L then
                                return false, H;
                            end if;
                        end for;
                    end for;
                end for;

                return true, H;
            else
                return false, H;
            end if;
        end if;

    else
        return false, H;
    end if;

end intrinsic;

/****************************************************************/
/* DELETE, Replaced by HadamardPhiZp_params                     */
/****************************************************************/
/*                                                              */
/* Function name: HadamardPhiZp                                 */
/* Parameters: u, H                                             */
/* Function description: It returns the image of u under the    */
/*   generalized Gray map given by H, denoted by Phi            */
/* Input parameters description:                                */
/*   - u: an element of Z/p^s                                   */
/*   - H: a generalized Hadamard matrix over GF(p) with zeros   */
/*        in the first row                                      */
/* Output parameters description:                               */
/*   - A vector over GF(p) as the image of u under Phi          */
/*                                                              */
/* Function developed by Javier Esmoris                         */
/*                                                              */
/****************************************************************/
HadamardPhiZp := function(u, H)
    nparyCoordinate := Ncols(H);
    p := #Parent(H[1][1]);
    s := Valuation(nparyCoordinate, p) + 1;
    V := VectorSpace(GF(p), nparyCoordinate);

    quotient, residue := Quotrem(Integers()!u, nparyCoordinate);
    firstTerm := V!H[residue + 1];
    secondTerm := V![quotient^^nparyCoordinate];

    return firstTerm + secondTerm;
end function;

/****************************************************************/
/*                                                              */
/* Function name: HadamardPhiZp_params                          */
/* Parameters: u, H, p, s, V                                    */
/* Function description: It returns the image of u under the    */
/*   generalized Gray map given by H, denoted by Phi            */
/* Input parameters description:                                */
/*   - u : an element of Z/p^s                                  */
/*   - H : a generalized Hadamard matrix over GF(p) with zeros  */
/*        in the first row                                      */
/*   - p : a prime number                                       */
/*   - s : an integer greater than 1                            */
/*   - V : the vector space over GF(p) of dimension Ncols(H)    */
/* Output parameters description:                               */
/*   - A vector over Zp as the image of u under Phi             */
/*                                                              */
/* Function developed by Javier Esmoris                         */
/*                                                              */
/****************************************************************/
HadamardPhiZp_params := function(u, H, p, s, V)
    nparyCoordinate := Ncols(H);
    quotient, residue := Quotrem(Integers()!u, nparyCoordinate);
    firstTerm := V!H[residue + 1];
    secondTerm := V![quotient^^nparyCoordinate];

    return firstTerm + secondTerm;
end function;

/****************************************************************/
/* DELETE, Replaced by HadamardPhiZp_params                     */
/****************************************************************/
/*                                                              */
/* Function name: HadamardPhiZpInverse                          */
/* Parameters: uPary, H                                         */
/* Function description: It returns the antiimage of uPary      */
/*   under the generalized Gray map given by H, denoted by Phi  */
/* Input parameters description:                                */
/*   - uPary: a vector over GF(p) of length p^(s-1)             */
/*   - H: a generalized Hadamard matrix over GF(p) with zeros   */
/*        in the first row                                      */
/* Output parameters description:                               */
/*   - An element of Z/p^s                                      */
/*                                                              */
/* Function developed by Javier Esmoris                         */
/*                                                              */
/****************************************************************/
HadamardPhiZpInverse := function(uPary, H)
    nparyCoordinate := Ncols(H);
    p := #Parent(uPary[1]);
    s := Valuation(nparyCoordinate, p) + 1;
    V := VectorSpace(GF(p), nparyCoordinate);

    lambda := uPary[1];
    pos := Position(Rows(H), uPary - V![lambda^^nparyCoordinate]) - 1;

    return pos + (Integers()!lambda)*nparyCoordinate;
end function;

/****************************************************************/
/*                                                              */
/* Function name: HadamardPhiZpInverse_params                   */
/* Parameters: uPary, H, p, s, V                                */
/* Function description: It returns the antiimage of uPary      */
/*   under the generalized Gray map given by H, denoted by Phi  */
/* Input parameters description:                                */
/*   - uPary : a vector over Zp of length p^(s-1)               */
/*   - H : a generalized Hadamard matrix over GF(p) with zeros  */
/*        in the first row                                      */
/*   - p : a prime number                                       */
/*   - s : an integer greater than 1                            */
/*   - V : the vector space over GF(p) of dimension Ncols(H)    */
/* Output parameters description:                               */
/*   - An element of Z/p^s                                      */
/*                                                              */
/* Function developed by Javier Esmoris                         */
/*                                                              */
/****************************************************************/
HadamardPhiZpInverse_params := function(uPary, H, p, s, V)
    nparyCoordinate := Ncols(H);
    lambda := uPary[1];
    pos := Position(Rows(H), uPary - V![lambda^^nparyCoordinate]) - 1;

    return pos + (Integers()!lambda)*nparyCoordinate;
end function;

/****************************************************************/
/*                                                              */
/* Function name: GrayMap                                       */
/* Parameters: H                                                */
/* Function description: Given a generalized Hadamard matrix H  */
/*   over GF(p) of length p^(s-1), for an integer s > 1, this   */
/*   function returns the generalized Gray map phi_s from Z/p^s */
/*   to GF(p)^(p^(s-1)) given by H. The matrix must have zeros  */
/*   in the first row, but it does not need to be normalized.   */
/* Input parameters description:                                */
/*   - H: a generalized Hadamard matrix over GF(p) with zeros   */
/*        in the first row                                      */
/* Output parameters description:                               */
/*   - The generalized Gray map given by H                      */
/*                                                              */
/* Function developed by Javier Esmoris                         */
/*                                                              */
/* Signature: (<AlgMatElt> H) -> Map                            */
/*                                                              */
/****************************************************************/
intrinsic GrayMap(H::AlgMatElt) -> Map
{
Given a generalized Hadamard matrix H over GF(p) of length p^(s-1), for an integer
s > 1, this function returns the generalized Gray map phi_s from Z/p^s to
GF(p)^(p^(s-1)) given by H. The matrix must have zeros in the first row,
but it does not need to be normalized. Matrix H can also be given as an ordinary
Hadamard matrix with 1's and -1's. In this case, it is transformed into a binary
matrix by swapping 1's for 0's and -1's for 1's.

Note that if H is the Sylvester Hadamard matrix, which is the matrix generated
by all linear combinations of the rows of a matrix Y_(s-1) of size (s-1) x p^(s-1)
whose columns are all the vectors in GF(p)^(s-1), then this map coincides with
the one given by function GrayMap(p, s).
}
    if Type(BaseRing(H)) eq RngInt then
        require IsHadamard(H): "Argument 1 must be a Hadamard matrix";
        H := OrdinaryMatrixToBinaryMatrix(H);
    else
        require Type(BaseRing(H)) eq FldFin and IsPrime(#BaseRing(H)):
                                     "Argument 1 must be a matrix over GF(p)";
        require IsHadamardMatrix(H): "Argument 1 must be a Hadamard matrix";
    end if;
    require Eltseq(H[1]) eq [0^^Ncols(H)]: "Argument 1 must have zeros in the first row";
    require Eltseq(Transpose(H)[1]) eq [0^^Ncols(H)]:
                                        "Argument 1 must have zeros in the first column";

    nparyCoordinate := Ncols(H);
    p := #Parent(H[1][1]);
    s := Valuation(nparyCoordinate, p) + 1;
    Zps := Integers(p^s);
    V := VectorSpace(GF(p), nparyCoordinate);

    return map< Zps -> V | x :-> HadamardPhiZp_params(x, H, p, s, V),
                           y :-> Zps!HadamardPhiZpInverse_params(y, H, p, s, V) >;

end intrinsic;

/****************************************************************/
/* DELETE, Replaced by HadamardPhiZp_params                     */
/****************************************************************/
/*                                                              */
/* Function name: HadamardPhiZpCodeword                         */
/* Parameters: c, H                                             */
/* Function description: It returns the image of the vector c   */
/*   over Z/p^s of length n under the generalized Gray map.     */
/*   The output is a vector over GF(p) of length (p^(s-1))n.    */
/* Input parameters description:                                */
/*   - c: a vector over Z/p^s of length n                       */
/*   - H: a generalized Hadamard matrix over GF(p) necessary to */
/*   compute the Gray map                                       */
/* Output parameters description:                               */
/*   - A vector over GF(p) of length (p^(s-1))n                 */
/*                                                              */
/* Function developed by Javier Esmoris                         */
/*                                                              */
/****************************************************************/
HadamardPhiZpCodeword := function(c, H)
    return &cat[Eltseq(HadamardPhiZp(u, H)) : u in Eltseq(c)];
end function;

/****************************************************************/
/*                                                              */
/* Function name: HadamardPhiZpCodeword_params                  */
/* Parameters: c, H, p, s, V                                    */
/* Function description: It returns the image of the vector c   */
/*   over Z/p^s of length n under the generalized Gray map.     */
/*   The output is a vector over Zp of length (p^(s-1))n.       */
/* Input parameters description:                                */
/*   - c : a vector over Z/p^s of length n                      */
/*   - H : a generalized Hadamard matrix over GF(p) necessary   */
/*         to compute the Gray map                              */
/*   - p : a prime number                                       */
/*   - s : an integer greater than 1                            */
/*   - V : the vector space over GF(p) of dimension Ncols(H)    */
/* Output parameters description:                               */
/*   - A vector over Zp of length (p^(s-1))n                    */
/*                                                              */
/****************************************************************/
HadamardPhiZpCodeword_params := function(c, H, p, s, V)
    return &cat[Eltseq(HadamardPhiZp_params(u, H, p, s, V)) : u in Eltseq(c)];
end function;

/****************************************************************/
/* DELETE, Replaced by HadamardPhiZp_params                     */
/****************************************************************/
/*                                                              */
/* Function name: HadamardPhiZpInverseCodeword                  */
/* Parameters: cPary, H, nparyCoordinate, n, V                  */
/* Function description: It returns the antiimage of the vector */
/*   cPary under the generalized Gray map. If the length of     */
/*   cPary is p^(s-1)*n for some integer n, then the output is  */
/*   a vector of (Z/p^s)^n.                                     */
/* Input parameters description:                                */
/*   - cPary: a vector over GF(p) of length (p^(s-1))n          */
/*   - H: a generalized Hadamard matrix over GF(p) necessary to */
/*        compute the Gray map                                  */
/*   - nparyCoordinate: number of GF(p) coordinates p^(s-1)     */
/*   - n: length of the output vector                           */
/*   - V: vector space over GF(p) of length nparyCoordinate     */
/* Output parameters description:                               */
/*   - A vector of (Z/p^s)^n (codeword)                         */
/*                                                              */
/* Function developed by Javier Esmoris                         */
/*                                                              */
/****************************************************************/
HadamardPhiZpInverseCodeword := function(cPary, H, nparyCoordinate, n, V)
    cParted := Partition(Eltseq(cPary), [nparyCoordinate^^n]);
    return &cat[[HadamardPhiZpInverse(V!i, H)] : i in cParted];
end function;

/****************************************************************/
/*                                                              */
/* Function name: HadamardPhiZpInverseCodeword_params           */
/* Parameters: cPary, H, n, p, s, V                             */
/* Function description: It returns the antiimage of the vector */
/*   cPary under the generalized Gray map. If the length of     */
/*   cPary is p^(s-1)*n for some integer n, then the output is  */
/*   a vector of Zps^n.                                         */
/* Input parameters description:                                */
/*   - cPary : a vector over Zp of length (p^(s-1))n            */
/*   - H : a generalized Hadamard matrix over Zp necessary to   */
/*        compute the Gray map                                  */
/*   - n : length of the output vector                          */
/*   - p : a prime number                                       */
/*   - s : an integer greater than 1                            */
/*   - V : the vector space over GF(p) of length Ncols(H)       */
/* Output parameters description:                               */
/*   - A vector of Zps^n (codeword)                             */
/*                                                              */
/****************************************************************/
HadamardPhiZpInverseCodeword_params := function(cPary, H, n, p, s, V)
    nparyCoordinate := Ncols(H);
    cParted := Partition(Eltseq(cPary), [nparyCoordinate^^n]);
    return &cat[[HadamardPhiZpInverse_params(V!i, H, p, s, V)] : i in cParted];
end function;

/****************************************************************/
/*                                                              */
/* Function name: GrayMap                                       */
/* Parameters: C, H                                             */
/* Function description: Given a linear code C over Z/p^s of    */
/*   length n and a generalized Hadamard matrix H over GF(p) of */
/*   order p^(s-1), for an integer s>1, this function returns   */
/*   the generalized Gray map Phi_s from C to GF(p)^(n*p^(s-1)) */
/*   given by H applied to each coordinate. The matrix must have*/
/*   zeros in the first row, but it does not need to be         */
/*   normalized.                                                */
/* Input parameters description:                                */
/*   - C : a linear code over Z/p^s of length n                 */
/*   - H : a generalized Hadamard matrix over GF(p) that defines*/
/*         the Gray map                                         */
/* Output parameters description:                               */
/*   - The Gray map from C to Zp^(n*p^(s-1))                    */
/*                                                              */
/* Function developed by Javier Esmoris                         */
/*                                                              */
/* Signature: (<CodeLinRng> C, <AlgMatElt> H) -> Map            */
/*                                                              */
/****************************************************************/
intrinsic GrayMap(C::CodeLinRng, H::AlgMatElt) -> Map
{
Given a linear code C over Z/p^s of length n and a generalized Hadamard matrix
H over GF(p) of order p^(s-1), for an integer s>1, this function returns the
generalized Gray map Phi_s from C to GF(p)^(n*p^(s-1)) given by H applied to
each coordinate. The matrix must have zeros in the first row, but it does not
need to be normalized. Matrix H can also be given as an ordinary Hadamard matrix
with 1's and -1's. In this case, it is transformed into a binary matrix by
swapping 1's for 0's and -1's for 1's.

Note that if H is the Sylvester Hadamard matrix, which is the matrix generated
by all linear combinations of the rows of a matrix Y_(s-1) of size (s-1) x p^(s-1)
whose columns are all the vectors in GF(p)^(s-1), then this map coincides with
the one given by function GrayMap(C).
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

    if Type(BaseRing(H)) eq RngInt then
        require IsHadamard(H): "Argument 1 must be a Hadamard matrix";
        H := OrdinaryMatrixToBinaryMatrix(H);
    else
        require Type(BaseRing(H)) eq FldFin and IsPrime(#BaseRing(H)):
                                     "Argument 1 must be a matrix over GF(p)";
        require IsHadamardMatrix(H): "Argument 1 must be a Hadamard matrix";
    end if;
    require Eltseq(H[1]) eq [0^^Ncols(H)]: "Argument 1 must have zeros in the first row";
    require Eltseq(Transpose(H)[1]) eq [0^^Ncols(H)]:
                                        "Argument 1 must have zeros in the first column";

    n := Length(C);
    nparyCoordinate := p^(s-1);
    V := VectorSpace(GF(p), nparyCoordinate);
    Vn := VectorSpace(GF(p), n*nparyCoordinate);

    return map< C -> Vn | c :-> Vn!HadamardPhiZpCodeword_params(c, H, p, s, V),
                          y :-> C!HadamardPhiZpInverseCodeword_params(y, H, n, p, s, V) >;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: GrayMapImage                                  */
/* Parameters: C, H                                             */
/* Function description: Given a linear code C over Z/p^s of    */
/*   length n and a generalized Hadamard matrix H over GF(p) of */
/*   order p^(s-1), for an integer s>1, this function returns   */
/*   the image of C under the generalized Gray map Phi_s from C */
/*   to GF(p)^(n*p^(s-1)) given by H applied to each coordinate.*/
/*   As the resulting image may not be a linear code over GF(p),*/
/*   a sequence of vectors in GF(p)^(n*p^(s-1)) is returned     */
/*   rather than a code. The matrix must have zeros in the first*/
/*   row, but it does not need to be normalized.                */
/* Input parameters description:                                */
/*   - C : a linear code over Z/p^s of length n                 */
/*   - H : a generalized Hadamard matrix over GF(p) that defines*/
/*         the Gray map                                         */
/* Output parameters description:                               */
/*   - A sequence of vectors of GF(p)^(n*p^(s-1))               */
/*                                                              */
/* Function developed by Javier Esmoris                         */
/*                                                              */
/* Signature: (<CodeLinRng> C, <AlgMatElt> H) -> [ModTupFldElt] */
/*                                                              */
/****************************************************************/
intrinsic GrayMapImage(C::CodeLinRng, H::AlgMatElt) -> SeqEnum
{
Given a linear code C over Z/p^s of length n and a generalized Hadamard matrix
H over GF(p) of order p^(s-1), for an integer s>1, this function returns the
image of C under the generalized Gray map Phi_s from C to GF(p)^(n*p^(s-1))
given by H applied to each coordinate. As the resulting image may not be a
linear code over GF(p), a sequence of vectors in GF(p)^(n*p^(s-1)) is returned
rather than a code. The matrix must have zeros in the first row, but it does
not need to be normalized. Matrix H can also be given as an ordinary Hadamard
matrix with 1's and -1's. In this case, it is transformed into a binary matrix
by swapping 1's for 0's and -1's for 1's.

Note that if H is the Sylvester Hadamard matrix, which is the matrix generated
by all linear combinations of the rows of a matrix Y_(s-1) of size (s-1) x p^(s-1)
whose columns are all the vectors in GF(p)^(s-1), then this map coincides with
the one given by function GrayMapImage(C).
}
    mapGray := GrayMap(C, H);

    return [mapGray(c) : c in C];

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: HasLinearGrayMapImage                         */
/* Parameters:  C, H                                            */
/* Function description: Given a linear code C over Z/p^s of    */
/*   length n and a generalized Hadamard matrix over GF(p) of   */
/*   order p^(s-1), for an integer s>1, this function returns   */
/*   true if and only if the image of C under the generalized   */
/*   Gray map Phi_s from C to GF(p)^(n*p^(s-1)) given by H      */
/*   applied to each coordinate, is a linear code over GF(p).   */
/*   If so, the function also returns the image C_p as a linear */
/*   code over GF(p), together with the bijection Phi_s:C->C_p. */
/* Input parameters description:                                */
/*   - C : a linear code over Z/p^s of length n                 */
/*   - H : a generalized Hadamard matrix over GF(p) that defines*/
/*         the Gray map                                         */
/* Output parameters description:                               */
/*   - true if and only if the image is a linear code over Zp.  */
/*     If return true, then                                     */
/*   - A linear code over Zp, 0 otherwise                       */
/*   - A map from C to B, 0 otherwise                           */
/*                                                              */
/* Signature: (<CodeLinRng> C, <AlgMatElt> H)                   */
/*                             -> BoolElt, CodeLinRng, Map      */
/*                                                              */
/****************************************************************/
intrinsic HasLinearGrayMapImage(C::CodeLinRng, H::AlgMatElt)
                                                     -> BoolElt, CodeLinRng, Map
{
Given a linear code C over Z/p^s of length n and a generalized Hadamard matrix
over GF(p) of order p^(s-1), for an integer s>1, this function returns true if
and only if the image of C under the generalized Gray map Phi_s from C to
GF(p)^(n*p^(s-1)) given by H applied to each coordinate, is a linear code
over GF(p). If so, the function also returns the image C_p as a linear code over
GF(p), together with the bijection Phi_s: C -> C_p. Matrix H can also be given
as an ordinary Hadamard matrix with 1's and -1's. In this case, it is transformed
into a binary matrix by swapping 1's for 0's and -1's for 1's.
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

        if Type(BaseRing(H)) eq RngInt then
        require IsHadamard(H): "Argument 1 must be a Hadamard matrix";
        H := OrdinaryMatrixToBinaryMatrix(H);
    else
        require Type(BaseRing(H)) eq FldFin and IsPrime(#BaseRing(H)):
                                     "Argument 1 must be a matrix over GF(p)";
        require IsHadamardMatrix(H): "Argument 1 must be a Hadamard matrix";
    end if;
    require Eltseq(H[1]) eq [0^^Ncols(H)]: "Argument 1 must have zeros in the first row";
    require Eltseq(Transpose(H)[1]) eq [0^^Ncols(H)]:
                                        "Argument 1 must have zeros in the first column";

    np := Length(C)*Ncols(H);

    B := GrayMapImage(C, H);
    V := VectorSpace(GF(p), np);
    S := sub< V | B >;

    if #B eq p^Dimension(S) then
        Cp := LinearCode(S);
        mapGray := GrayMap(C, H);
        bijection := map<C -> Cp  | v :-> mapGray(v), w :-> w @@ mapGray >;
        return true, Cp, bijection;
    else
        return false, 0, 0;
    end if;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////    STANDARD FORMS OF GENERATOR MATRICES FOR CODES OVER Z/p^s    ////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/******************************************************************************/
/*                                                                            */
/* Function name: ZpStandardForm                                              */
/* Parameters:  C                                                             */
/* Function description: Given a linear code C over Z/p^s, return a           */
/*   permutation-equivalent code S in standard form, together with the        */
/*   corresponding isomorphism from C onto S. It also returns the generator   */
/*   matrix in standard form used to generate the code S and the permutation  */
/*   x such that C^x = S. Magma returns one of the many codes in standard     */
/*   form which is isomorphic to C (the same code is returned each time).     */
/* Input parameters description:                                              */
/*   - C : A linear code over Z/p^s                                           */
/* Output parameters description:                                             */
/*   - A permutation-equivalent code S in standard form                       */
/*   - A map from C to S                                                      */
/*   - A generator matrix in standard form                                    */
/*   - A permutation transforming C into S                                    */
/*                                                                            */
/* Function developed by Noam von Rotberg                                     */
/*                                                                            */
/* Signature: (<CodeLinRng> C) -> CodeLinRng, Map, ModMatRngElt, GrpPermElt   */
/*                                                                            */
/******************************************************************************/
intrinsic ZpStandardForm(C::CodeLinRng : IsReducedStandardForm := false)
                            -> CodeLinRng, Map, ModMatRngElt, GrpPermElt
{
Given a linear code C over Z/p^s, return a permutation-equivalent code S in
standard form, together with the corresponding isomorphism from C onto
S. It also returns the generator matrix in standard form used to generate
the code S and the permutation x such that C^x = S. Magma returns one of
the many codes in standard form which is isomorphic to C (the same code
is returned each time).

The parameter IsReducedStandardForm specifies whether the generator matrix
is given as a matrix in reduced standard form. The default value is false.
If it is set to true, the function returns a generator matrix which is in
reduced standard form.

If C is a linear code over Z4, the first two output parameters coincide with
the ones given by the function StandardForm(C), and the last two parameters
with the first and forth ones given by StandardFormInfo(C).
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

    Gs, _, _, perm := StandardFormInfo(C);

    if IsReducedStandardForm then
        Gs := EchelonForm(Gs);
    end if;

    Cs := LinearCode(Gs);
    f := map< C -> Cs | v :-> v^perm, w :-> w^(perm^(-1))>;

    return Cs, f, Gs, perm;

end intrinsic;

/******************************************************************************/
/*                                                                            */
/* Function name: IsStandardFormMatrix                                        */
/* Parameters:  G                                                             */
/* Function description: Given a matrix G over Z/p^s, return true if and only */
/*   if G is a generator matrix in standard form.                             */
/*   The parameter IsReducedStandardForm is set to false by default. If it is */
/*   set to true, the function returns true if and only if G is in reduced    */
/*   standard form.                                                           */
/* Input parameters description:                                              */
/*   - G : a matrix over a ring Z/p^s                                         */
/*   - IsInStandardFormMatrix : a Boolean                                     */
/* Output parameters description:                                             */
/*   - true if and only if G is in standard form                              */
/*                                                                            */
/* Function developed by Noam von Rotberg                                     */
/*                                                                            */
/* Signature: (<Mtrx> G) -> BoolElt                                           */
/*                                                                            */
/******************************************************************************/
intrinsic IsStandardFormMatrix(G::Mtrx : IsReducedStandardForm := false) -> BoolElt
{
Given a matrix G over Z/p^s, return true if and only if G is a generator matrix
in standard form.

The parameter IsReducedStandardForm is set to false by default. If it is set to
true, the function returns true if and only if G is in reduced standard form.
}
    isOverZps, p, s := IsMatrixOverZps(G);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

    n := NumberOfColumns(G);
    k := NumberOfRows(G);
    if not (n ge k) or (n eq 0) then
        return false;
    end if;

    type := [ Multiplicity( Diagonal(G), p^i ) : i in [0..(s-1)] ];
    if not k eq &+type then
        return false;
    end if;

    if not IsUpperTriangular(G) then
        return false;
    end if;

    Zps := BaseRing(G);
    for i in [1..s] do
        sum := (i eq 1) select 0 else (&+[type[j] : j in [1..i-1]]);

        identityMatrix := ExtractBlock(G, sum+1, sum+1, type[i], type[i]);
        if not identityMatrix eq p^(i-1)*IdentityMatrix(Zps, type[i]) then
            return false;
        end if;

        randomMatrix := ExtractBlock(G, sum+1, sum + type[i] +1, type[i],
                                                        n - sum - type[i]);
        if not IsZero(p^(s-i+1)*randomMatrix) then
            return false;
        end if;
    end for;

    if IsReducedStandardForm then
        if not EchelonForm(G) eq G then
            return false;
        end if;
    end if;

    return true;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: ZpTypeSequence                                */
/* Parameters: G, p, s                                          */
/* Function description: Given a generator matrix in standard   */
/*   form over Z/p^s, the prime number p, and the positive      */
/*   integer s, the function returns the sequence [t1,...,ts]   */
/*   corresponding to the type of the code generated by G.      */
/* Input parameters description:                                */
/*   - G : A matrix over Z/p^s                                  */
/*   - p : A prime number                                       */
/*   - s : A positive integer                                   */
/* Output parameters description:                               */
/*   - A sequence containing the type [t1,t2,...,ts]            */
/*                                                              */
/****************************************************************/
ZpTypeSequence := func<G, p, s | [ Multiplicity( Diagonal(G), p^i ) : i in [0..(s-1)] ]>;

/******************************************************************************/
/*                                                                            */
/* Function name: ZpMinRowsGeneratorMatrix                                    */
/* Parameters:  C                                                             */
/* Function description: A generator matrix for the linear code C over Z/p^s  */
/*   of type (n; t1,...,ts), with the minimum number of rows, that is with    */
/*   t1+...+ts rows: t1 rows of order p^s, t2 of order p^(s-1), and so on     */
/*   until ts rows of order p. It also returns the sequence [t1,...,ts] and a */
/*   permutation transforming C into a permutation-equivalent code with       */
/*   generator matrix in standard form.                                       */
/* Input parameters description:                                              */
/*   - C : A linear code over Z/p^s                                           */
/* Output parameters description:                                             */
/*   - A generator matrix with the minimum number of rows                     */
/*   - A sequence containing the type of C: [t1,t2,...,ts]                    */
/*   - A permutation transforming C into S                                    */
/*                                                                            */
/* Function updated by Adrián Torres                                          */
/*                                                                            */
/* Signature: (<CodLinRng> C) -> ModMatRngElt, SeqEnum, GrpPermElt            */
/*                                                                            */
/******************************************************************************/
intrinsic ZpMinRowsGeneratorMatrix(C::CodeLinRng) -> ModMatRngElt, SeqEnum, GrpPermElt
{
A generator matrix for the linear code C over Z/p^s of type (n; t1,...,ts), with the
minimum number of rows, that is with t1+...+ts rows: t1 rows of order p^s, t2 of order
p^(s-1), and so on until ts rows of order p. It also returns the sequence [t1,...,ts]
and a permutation transforming C into a permutation-equivalent code with generator
matrix in standard form.

If C is a linear code over Z4 of type (n; t1, t2), to obtain a generator matrix with
minimum number of rows, function MinRowsGeneratorMatrix(C) can also be used. However,
instead of returning the sequence [t1, t2], it returns t2, t1, and the generator matrix
may be different.
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

    Gs, _, _, perm := StandardFormInfo(C);
    Gmin := Gs^(perm^(-1));

    return Gmin, ZpTypeSequence(Gs, p, s), perm;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////               INVARIANTS OF CODES OVER Z/p^s                    ////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/******************************************************************************/
/*                                                                            */
/* Function name: ZpPseudoDimension                                           */
/* Parameters: C                                                              */
/* Function description: Given a linear code C over Z/p^ s of type (n; t1,..  */
/*   ts), return the value st_1+(s-1)t_2+... + t_s. Note that                 */
/*   |C|=p^(st_1+(s-1)t_2+\dots + t_s). Function PseudoDimension(C), for      */
/*   linear codes over rings in general, return the number of generators of   */
/*   the linear code C, that is, t_1+t_2+...+t_s. return the information rate */
/*   of C, that is the ratio (st1 + (s-1)t2 + ...+ ts) / (n*s).               */
/* Input parameters description:                                              */
/*   - C: A linear code over Z/p^s                                            */
/* Output parameters description:                                             */
/*   - The dimension of C with respect to p, that is, Log_p(|C|)              */
/*                                                                            */
/* Signature: (<CodeLinRng> C) -> IntRngElt                                   */
/*                                                                            */
/******************************************************************************/
intrinsic ZpPseudoDimension(C::CodeLinRng) -> IntRngElt
{
Given a linear code C over Z/p^s of type (n; t1,..ts), return the value st_1+(s-1)t_2+... + t_s.
Note that |C|=p^(st_1+(s-1)t_2+\dots + t_s). Function PseudoDimension(C), for linear codes over
rings in general, return the number of generators of the linear code C, that is, t_1+t_2+...+t_s.
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 1): "The code C must be over Z/p^s with p prime and s>=1";

    type := ZpType(C);
    return &+[ type[i]*(s-i+1) : i in [1..s] ];

end intrinsic;

/******************************************************************************/
/*                                                                            */
/* Function name: ZpInformationRate                                           */
/* Parameters: C                                                              */
/* Function description: Given a linear code C over Z/p^ s of type (n; t1,..  */
/*   ts), return the information rate of C, that is the ratio                 */
/*   (st1 + (s-1)t2 + ...+ ts) / (n*s).                                       */
/* Input parameters description:                                              */
/*   - C: A linear code over Z/p^s                                            */
/* Output parameters description:                                             */
/*   - The information rate of C                                              */
/*                                                                            */
/* Signature: (<CodeLinRng> C) -> FldRatElt                                   */
/*                                                                            */
/******************************************************************************/
intrinsic ZpInformationRate(C::CodeLinRng) -> FldRatElt
{
Given a linear code C over Z/p^s of type (n; t1,..ts), return the information rate of C,
that is the ratio (st1 + (s-1)t2 + ...+ ts) / (n*s).
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 1): "The code C must be over Z/p^s with p prime and s>=1";

    return Log(p, #C) / (Length(C)*s);

end intrinsic;

/******************************************************************************/
/*                                                                            */
/* Function name: ZpType                                                      */
/* Parameters:  C                                                             */
/* Function description: Given a linear code C over Z/p^s of length n, return */
/*   the type of the code, that is, the unique sequence [t1,...,ts] such that */
/*   the code, as a subgroup of (Z/p^s)^n, is isomorphic to (Z/p^s)^t1 x      */
/*   (Z/p^(s-1))^t2 x ··· x Zp^ts.                                            */
/* Input parameters description:                                              */
/*   - C : A linear code over Z/p^s                                           */
/* Output parameters description:                                             */
/*   - A sequence containing the type of C: [t1,t2,...,ts]                    */
/*                                                                            */
/* Function developed by Guillermo Mosse                                      */
/*          and updated by Adrián Torres                                      */
/*                                                                            */
/* Signature: (<CodeLinRng> C) -> SeqEnum                                     */
/*                                                                            */
/******************************************************************************/
intrinsic ZpType(C::CodeLinRng) -> SeqEnum
{
Given a linear code C over Z/p^s of length n, return the type of the code,
that is, the unique sequence [t1,...,ts] such that the code, as a subgroup
of (Z/p^s)^n, is isomorphic to (Z/p^s)^t1 x (Z/p^(s-1))^t2 x ··· x Zp^ts.
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

    return ZpTypeSequence(StandardFormInfo(C), p, s);

end intrinsic;

/******************************************************************************/
/*                                                                            */
/* Function name: ZpTypeDual                                                  */
/* Parameters:  C                                                             */
/* Function description: Given a linear code C over Z/p^s of type (n; t1,..., */
/*   ts), return the type of the dual code of C, that is, the sequence        */
/*   [n-t1-t2-...-ts, ts, ..., t2].                                           */
/* Input parameters description:                                              */
/*   - C : A linear code over Z/p^s                                           */
/* Output parameters description:                                             */
/*   - A sequence containing the type of the dual code of C                   */
/*                                                                            */
/* Function developed by Merce Villanueva                                     */
/*                                                                            */
/* Signature: (<CodeLinRng> C) -> SeqEnum                                     */
/*                                                                            */
/******************************************************************************/
forward ZpTypeDual;
intrinsic ZpTypeDual(C::CodeLinRng) -> SeqEnum
{
Given a linear code C over Z/p^s of type (n; t1,...,ts), return the type of
the dual code of C, that is, the sequence [n-t1-t2-...-ts, ts, ..., t2].
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

    type := ZpType(C);
    n := Length(C);

    return [n - &+type] cat Reverse(type[2..#type]);

end intrinsic;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////            THE DUAL CODE AND RELATED FUNCTIONS                  ////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */
/* Function name: DivideMatrix                                  */
/* Parameters:  G, p, T                                         */
/* Function description: Let G be a matrix over Z/p^s with the  */
/*   first t1 rows of order p^s, the second t2 rows of order    */
/*   p^(s-1), ..., and the last ts rows of order p. This        */
/*   function returns the matrix obtained from dividing rows of */
/*   order p^t by p^(s-t).                                      */
/* Input parameters description:                                */
/*   - G : A matrix over Z/p^s                                  */
/*   - p : A prime number                                       */
/*   - T : A sequence with nonnegative integers t1,...,ts       */
/* Output parameters description:                               */
/*   - A matrix over Z/p^s                                      */
/*                                                              */
/* Function developed by Adrián Torres                          */
/*                                                              */
/****************************************************************/
DivideMatrix := function(G, p, T)
    n := Ncols(G);
    row := T[1]+1;
    for t in [2..#T] do
        divisor := p^(t-1);
        for i in [1..T[t]] do
            for col in [1..n] do
                G[row, col] := G[row, col] div divisor;
            end for;
            row +:= 1;
        end for;
    end for;

    return G;
end function;

/****************************************************************/
/*                                                              */
/* Function name: StandardFormParityCheckMatrix                 */
/* Parameters:  Gs, p, n, type                                  */
/* Function description: Given a matrix Gs over Z/p^s in        */
/*   standard form, the prime number p, and the positive number */
/*   s, the function returns a parity check matrix of the code  */
/*   generated by Gs, which corresponds to the one described    */
/*   in the given reference.                                    */
/*                                                              */
/* Input parameters description:                                */
/*   - G : A matrix over Z/p^s                                  */
/*   - p : A prime number                                       */
/*   - n : A positive integer                                   */
/*   - T : A sequence with nonnegative integers t1,...,ts       */
/* Output parameters description:                               */
/*   - A matrix over Z/p^s                                      */
/*                                                              */
/* Reference: "Computing efficiently a parity-check matrix for  */
/*   Z/p^s-linear codes", by C. Fernández-Córdoba, A. Torres-   */
/*   Martí, Carlos Vela and M. Villanueva, submitted to IEEE    */
/*   Trans. Inf. Theory, 2023.                                  */
/*                                                              */
/* Function developed by Adrián Torres                          */
/*                                                              */
/****************************************************************/
StandardFormParityCheckMatrix := function(Gs, p, s)
    Zps := Integers(p^s);
    type := ZpTypeSequence(Gs, p, s);
    n := Ncols(Gs);

    Gp := DivideMatrix(Gs, p, type);

    fullType := &+type;
    H := ZeroMatrix(Zps, n-type[1], n);

    Col := -Submatrix(Gp, fullType-type[s]+1, fullType+1, type[s], n-fullType);
    pos := fullType+1-type[s];
    for i in [2..s] do
        t := type[s-i+1];
        lastRow := Submatrix(Gp, pos-t, pos, t, fullType-pos+1);
        lastRowRedundancy := Submatrix(Gp, pos-t, fullType+1, t, n-fullType);
        Col := VerticalJoin(-lastRowRedundancy-lastRow*Col, Col);
        pos -:= t;
    end for;
    InsertBlock(~H, HorizontalJoin(Transpose(Col), IdentityMatrix(Zps, n-&+type)), 1, 1);
    zeros := n-&+type;
    for j in [2..s] do
        Col := p^(j-1)*IdentityMatrix(Zps, type[s-j+2]);
        pos := &+type[1..(s-j+1)] + 1;
        for i in [j..s] do
            t := type[s-i+1];
            lastRow := Submatrix(Gp, pos-t, pos, t, n-zeros-pos+1);
            Col := VerticalJoin(-lastRow*Col, Col);
            pos -:= t;
        end for;
        InsertBlock(~H, Transpose(Col), zeros+1, 1);
        zeros +:= type[s-j+2];
    end for;

    return H;
end function;

/*******************************************************************************/
/*                                                                             */
/* Function name: ZpDual  (Iterative version)                                  */
/* Parameters:  C                                                              */
/* Function description: Given a linear code C over Z/p^s of type (n; t1,...,  */
/*   ts), return the dual code D of C. The dual code consists of all codewords */
/*   in the (Z/p^s)-space V=(Z/p^s)^n which are orthogonal to all codewords of */
/*   C. In particular, the dual code D is of type (n; n-t1-t2-...-ts, ts,      */
/*   t_(s-1),..., t_2).                                                        */
/* Input parameters description:                                               */
/*   - C : A linear code over Z/p^s                                            */
/* Output parameters description:                                              */
/*   - The dual code of C                                                      */
/*                                                                             */
/* Function developed by Adrián Torres                                         */
/*                                                                             */
/*******************************************************************************/
intrinsic ZpDual(C::CodeLinRng) -> CodeLinRng
{
Given a linear code C over Z/p^s of type (n; t1,...,ts), return the dual code
D of C. The dual code consists of all codewords in the (Z/p^s)-space V=(Z/p^s)^n
which are orthogonal to all codewords of C. In particular, the dual code D is of
type (n; n-t1-t2-...-ts, ts, t_(s-1),..., t_2).

This function creates the generator matrix of D using a specific known structure
based on the generator matrix of C. This construction improves the computation
time with respect to the generic function Dual(C) for codes over rings.

If C is over Z4, function ZpDual(C) coincides with function DualZ4(C), but the
former may perform less efficiently in general.
}
	isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2) : "Argument 1 must be a code over Zps, with s>1.";

    Gs, _, _, perm := StandardFormInfo(C);
    Hs := StandardFormParityCheckMatrix(Gs, p, s);

    return LinearCode(Hs^(perm^(-1)));

end intrinsic;

/******************************************************************************/
/*                                                                            */
/* Function name: ZpStandardFormDual                                          */
/* Parameters:  C                                                             */
/* Function description: Given a linear code C over Z/p^s, return the dual of */
/*   a permutation-equivalent code S in standard form, together with the      */
/*   corresponding isomorphism from the dual of C onto the dual of S. It also */
/*   returns the parity check matrix used to generate the dual code of S and  */
/*   the permutation x such that (C^\perp)^x = S^\perp. Magma returns one of  */
/*   the many codes which is isomorphic to C^\perp (the same code is returned */
/*   each time).                                                              */
/*                                                                            */
/* Input parameters description:                                              */
/*   - C : A linear code over Z/p^s                                           */
/* Output parameters description:                                             */
/*   - The dual of a permutation-equivalent code S in standard form           */
/*   - A map from the dual of C to the dual of S                              */
/*   - A parity check matrix of C                                             */
/*   - A permutation transforming the dual of C into the dual of S            */
/*                                                                            */
/* Function developed by Merce Villanueva                                     */
/*                                                                            */
/* Signature: (<CodeLinRng> C) -> CodeLinRng, Map, ModMatRngElt, GrpPermElt   */
/*                                                                            */
/******************************************************************************/
intrinsic ZpStandardFormDual(C::CodeLinRng) -> CodeLinRng, Map, ModMatRngElt,
                                               GrpPermElt
{
Given a linear code C over Z/p^s, return the dual of a permutation-equivalent
code S in standard form, together with the corresponding isomorphism from the
dual of C onto the dual of S. It also returns the parity check matrix used to
generate the dual code of S and the permutation x such that (C^\perp)^x = S^\perp.
Magma returns one of the many codes which is isomorphic to C^\perp (the same
code is returned each time).

If C is a linear code over Z4, the first two output parameters coincide with
the ones given by the function StandardFormDual(C).
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

    Gs, _, _, perm := StandardFormInfo(C);
    Hs := StandardFormParityCheckMatrix(Gs, p, s);

    D := LinearCode(Hs^(perm^(-1)));
    Ds := LinearCode(Hs);
    f := map< D -> Ds | v :-> v^perm, w :-> w^(perm^(-1))>;

    return Ds, f, Hs, perm;

end intrinsic;

/******************************************************************************/
/*                                                                            */
/* Function name: ZpMinRowsParityCheckMatrix                                  */
/* Parameters:  C                                                             */
/* Function description: A parity check matrix for the linear code C over     */
/*   Z/p^s of type (n; t1,...,ts), with the minimum number of rows, that is,  */
/*   with n-t1 rows. It also returns the sequence [n-t1-t2-...-ts, ts, ...,   */
/*   t2] and a permutation transforming C^\perp into a permutation-equivalent */
/*   code with generator matrix in standard form.                             */
/* Input parameters description:                                              */
/*   - C : A linear code over Z/p^s                                           */
/* Output parameters description:                                             */
/*   - A parity check matrix with the minimum number of rows                  */
/*   - A sequence containing the type of the dual of C                        */
/*   - A permutation transforming the dual of C into the dual of S            */
/*                                                                            */
/* Function developed by Mercè Villanueva                                     */
/*                                                                            */
/* Signature: (<CodLinRng> C) -> ModMatRngElt, SeqEnum, GrpPermElt            */
/*                                                                            */
/******************************************************************************/
intrinsic ZpMinRowsParityCheckMatrix(C::CodeLinRng) -> ModMatRngElt, SeqEnum, GrpPermElt
{
A parity check matrix for the linear code C over Z/p^s of type (n; t1,...,ts), with the
minimum number of rows, that is, with n-t1 rows. It also returns the sequence
[n-t1-t2-...-ts, ts, ..., t2] and a permutation transforming C^\perp into a
permutation-equivalent code with generator matrix in standard form.

This function should be faster for most codes over Z/p^s than the general function
ParityCheckMatrix(C) for codes over finite rings. Another parity check matrix for the
code C can be obtained as the generator matrix of the dual of C with the minimum number
of rows, that is, as ZpMinRowsGeneratorMatrix(ZpDual(C)).

If C is a linear code over Z4 of type (n; t1, t2), then MinRowsParityCheckMatrix(C)
can also be used to obtain a parity check matrix with minimum number of rows. However,
only the matrix is returned, which may not coincide with the one given by
ZpMinRowsGeneratorMatrix(C).
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

    Gs, _, _, perm := StandardFormInfo(C);
    Hs := StandardFormParityCheckMatrix(Gs, p, s);
    Hmin := Hs^(perm^(-1));

    return Hmin, ZpTypeDual(C), perm;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////                   COSET REPRESENTATIVES                         ////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/*******************************************************************************/
/*                                                                             */
/* Function name: CosetRepresentatives                                         */
/* Parameters:  C                                                              */
/* Function description: Given a linear code C over Z/p^s of length n, with    */
/*   ambient space V = (Z/p^s)^n, return a set of coset representatives (not   */
/*   necessarily of minimal weight in their cosets) for C in V as an indexed   */
/*   set of vectors from V. The set of coset representatives {c_0, c_1,...,c_t}*/
/*   satisfies that c_0 is the zero codeword and V = U_(i=0)^t (C + c_i).      */
/*   Note that this function is only applicable when V and C are small.        */
/* Input parameters description:                                               */
/*   - C : A linear code over Z/p^s                                            */
/* Output parameters description:                                              */
/*   - A sequence containing the coset representatives c_0, c_1,..., c_t       */
/*                                                                             */
/* Function developed by Mercè Villanueva                                      */
/*          and generalized by Adrián Torres                                   */
/*                                                                             */
/* Signature: (<CodLinRng> C) -> SetIndx                                       */
/*                                                                             */
/*******************************************************************************/
intrinsic CosetRepresentatives(C::CodeLinRng) -> SetIndx
{
Given a linear code C over Z/p^s of length n, with ambient space V = (Z/p^s)^n,
return a set of coset representatives (not necessarily of minimal weight in their
cosets) for C in V as an indexed set of vectors from V. The set of coset
representatives [c_0, c_1,..., c_t] satisfies that c_0 is the zero codeword and
V = U_(i=0)^t (C + c_i). Note that this function is only applicable when V and
C are small.
}
	isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code C must be over Z/p^s with s>1";

    Zps := Integers(p^s);
    U := UniverseCode(Zps, Length(C));

    leadersSeq := [];
    if (#C eq 1) then
        leadersSeq := {@ x : x in U @};
    elif (#C eq #U) then
        leadersSeq := {@ U!0 @};
    else
        Q, f := quo<RSpace(U)|RSpace(C)>;
        R := RSpace(Zps, Degree(Q));
        leadersSeq := {@ (Q!x)@@f : x in R @};
    end if;

    return leadersSeq;

end intrinsic;

/*******************************************************************************/
/*                                                                             */
/* Function name: CosetRepresentatives                                         */
/* Parameters:  C, S                                                           */
/* Function description: Given a linear code C over Z/p^s of length n, and a   */
/*   subcode S over Z/p^s of C, return a set of coset representatives (not     */
/*   necessarily of minimal weight in their cosets) for S in C as an indexed   */
/*   set of codewords from C. The set of coset representatives [c_0, c_1,...,  */
/*   c_t] satisfies that c_0 is the zero codeword and C = U_(i=0)^t (S + c_i). */
/*   The function also returns a second set containing the images of the coset */
/*   representatives [c_0, c_1,..., c_t] by Carlet's generalized Gray map.     */
/*   Note that this function is only applicable when S and C are small.        */
/* Input parameters description:                                               */
/*   - C : A code over Zps                                                     */
/*   - S : A subcode over Zps of C                                             */
/* Output parameters description:                                              */
/*   - A sequence containing the coset representatives c_0, c_1,..., c_t       */
/*   - A sequence containing the Gray map image of the coset representatives   */
/*                                                                             */
/* Function developed by Mercè Villanueva                                      */
/*          and generalized by Adrián Torres                                   */
/*                                                                             */
/* Signature: (<CodLinRng> C, <CodLinRng> S) -> SetIndx, SetIndx               */
/*                                                                             */
/*******************************************************************************/
intrinsic CosetRepresentatives(C::CodeLinRng, S::CodeLinRng) -> SetIndx, SetIndx
{
Given a linear code C over Z/p^s of length n, and a subcode S over Z/p^s of C,
return a set of coset representatives (not necessarily of minimal weight in their
cosets) for S in C as an indexed set of codewords from C. The set of coset
representatives [c_0, c_1,..., c_t] satisfies that c_0 is the zero codeword and
C = U_(i=0)^t (S + c_i). The function also returns a second set containing the
images of the coset representatives [c_0, c_1,..., c_t] by Carlet's generalized
Gray map. Note that this function is only applicable when S and C are small.
}
	isOverZps, p, s := IsLinearCodeOverZps(C);
    isOverZpsS, _, _ := IsLinearCodeOverZps(S);
    require isOverZps and (s ge 2) : "Argument 1 must be a code over Zps with s>1";
    require isOverZpsS and (s ge 2) : "Argument 2 must be a code over Zps with s>1";
    require (S subset C) : "Argument 2 must be a subcode of argument 1";

    fp := CarletGrayMap(C);
    Q, f := quo<RSpace(C)|RSpace(S)>;
    degreeQ := Degree(Q);
    if degreeQ gt 0 then
        R := RSpace(Integers(p^s), degreeQ);
        leadersZps := {@ (Q!x)@@f : x in R @};
        leadersGFp := {@ fp(v) : v in leadersZps @};
    else
        leadersZps := {@ C!0 @};
        leadersGFp := {@ fp(C!0) @};
    end if;

    return leadersZps, leadersGFp;

end intrinsic;
