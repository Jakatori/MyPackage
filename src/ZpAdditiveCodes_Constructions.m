////////////////////////////////////////////////////////////////////////////////
/////////       Copyright 2015-2023 Cristina Fernández-Córdoba,         ////////
/////////      Dipak K. Bhunia, Adrián Torres and Mercè Villanueva      ////////
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
/* File name: ZpAdditiveCodes_Constructions.m                */
/*                                                           */
/* Comment: Package developed within the CCSG group          */
/*                                                           */
/* Authors: Dipak K. Bhunia, Carlos Vela,                    */
/*          C. Fernández-Córdoba and Mercè Villanueva        */
/*                                                           */
/* Revision version and last date:       v1.0   10-02-2023   */
/*  (moved from ZpAdditiveCodes_Core v1.6)                   */
/*                                       v2.0   22-12-2023   */
/*                                                           */
/*************************************************************/
//Uncomment freeze when package finished
//freeze

intrinsic ZpAdditiveCodes_Constructions_version() -> SeqEnum
{Return the current version of this package.}

    version := [2, 0];
    return version;

end intrinsic;

/****************************************************************
    GLOBAL VARIABLES
*****************************************************************/

import "ZpAdditiveCodes_Core.m": IsLinearCodeOverZps;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////                  RANDOM CODES OVER Z/p^s                        ////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */
/* Function name: RandomZpAdditiveCode                          */
/* Parameters:  p, n, L                                         */
/* Function description: Given a prime p, a positive integer n, */
/*   and a sequence L=[t_1,...,t_s] of s>=2 nonnegative         */
/*   integers, return a random linear code over Z/p^s of type   */
/*   (n; t_1,...,t_s). The function also returns the matrix     */
/*   used to generate the random code, which is in standard     */
/*   form.                                                      */
/* Input parameters description:                                */
/*   - p : A prime number                                       */
/*   - n : A positive integer                                   */
/*   - L : A sequence of s nonnegative integers                 */
/* Output parameters description:                               */
/*   - A random linear code over Z/p^s of type (n; L)           */
/*   - A generator matrix of the code in standard form          */
/*                                                              */
/* Function developed by Noam von Rotberg                       */
/*                                                              */
/* Signature: (<RngIntElt> p, <RngIntElt> n, <[RngIntElt]> L)   */
/*                                 -> CodeLinFld, ModMatRngElt  */
/*                                                              */
/****************************************************************/
intrinsic RandomZpAdditiveCode(p::RngIntElt, n::RngIntElt, L::[RngIntElt])
                                                -> CodeLinRng, ModMatRngElt
{
Given a prime p, a positive integer n, and a sequence L=[t1,...,ts] of s>=2
nonnegative integers, return a random linear code over Z/p^s of type
(n; t1,...,ts). The function also returns the matrix used to generate
the random code, which is in standard form.
}
    require IsPrime(p): "Argument 1 must be a prime number";
    require n ge 1: "Argument 2 must be a positive integer";
    s := #L;
    require s ge 2: "Argument 3 must be a sequence with at least two elements";
    require Min(L) ge 0: "Argument 3 must be a sequence of nonnegative integers";
    require n ge &+[ t : t in L ]: "Argument 2 must be greater than or equal to
                                    the sum over the entries in Argument 3";

    Zps := Integers(p^s);

    G := HorizontalJoin( IdentityMatrix(Zps, L[1]),
                         RandomMatrix  (Zps, L[1], n - L[1]) );
    for i in {2..s} do
        G := VerticalJoin( G, HorizontalJoin(<
                    ZeroMatrix    (Zps, L[i], &+[ L[j] : j in {1..i-1}] ),
            p^(i-1)*IdentityMatrix(Zps, L[i]),
            p^(i-1)*RandomMatrix  (Zps, L[i], n - &+[ L[j] : j in {1..i}] )
        >));
    end for;

    return LinearCode(G), G;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: RandomZpAdditiveCode                          */
/* Parameters:  p, n, s, k                                      */
/* Function description: Given a prime p, and three positive    */
/*   integers n, s, and k such that s>=2 and k<=n, return a     */
/*   random linear code over Z/p^s of type (n; t1,...,ts) such  */
/*   that t1+...+ts=k. The function also returns the matrix used*/
/*   to generate the random code, which is in standard form.    */
/* Input parameters description:                                */
/*   - p : A prime number                                       */
/*   - n : A positive integer                                   */
/*   - s : A positive integer such that s>1                     */
/*   - k : A poditive integer such that k<=n                    */
/* Output parameters description:                               */
/*   - A random linear code over Z/p^s of type (n; L)           */
/*   - A generator matrix of the code in standard form          */
/*                                                              */
/* Function developed by Mercè Villanueva                       */
/*                                                              */
/* Signature: (<RngIntElt> p, <RngIntElt> n, <RngIntElt> s,     */
/*             <RngIntElt> k) -> CodeLinFld, ModMatRngElt       */
/*                                                              */
/****************************************************************/
intrinsic RandomZpAdditiveCode(p::RngIntElt, n::RngIntElt, s::RngIntElt,
                               k::RngIntElt) -> CodeLinRng, ModMatRngElt
{
Given a prime p, and three positive integers n, s, and k such that s>=2 and k<=n,
return a random linear code over Z/p^s of type (n; t1,...,ts) such that
t1+...+ts=k. The function also returns the matrix used to generate the random code,
which is in standard form.

This function generates a random sequence [t1,...,ts] such that t1+...+ts=k, and
then it uses RandomZpAdditiveCode(p, n, [t1,...,ts]). Note that it does not use
function RandomLinearCode(Integers(p^s), n, k) available in Magma.
}
    require IsPrime(p): "Argument 1 must be a prime number";
    require n ge 1: "Argument 2 must be a positive integer";
    require s ge 2: "Argument 3 must be greater than 1";
    require n ge k: "Argument 2 must be greater than or equal to Argument 4";

    L := [Random(k)];
    for i in [2..s-1] do
        Append(~L, Random(k - &+L));
    end for;
    Append(~L, k - &+L);

    C, G := RandomZpAdditiveCode(p, n, L);
    return C, G;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////                    DERIVED CODES OVER Fq                        ////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */
/* Function name: ZpResidueCode                                 */
/* Parameters:  C                                               */
/* Function description: Given a linear code C over Z/p^s of    */
/*   type (n; t1,...,ts), return the code over GF(p) formed by  */
/*   taking each codeword in C modulo p. This is known as the   */
/*   residue code of C.                                         */
/* Input parameters description:                                */
/*   - C : A linear code over Z/p^s                             */
/* Output parameters description:                               */
/*   - The residue code of C as a linear code over GF(p)        */
/*                                                              */
/* Function developed by Abdullah Irfan Basheer                 */
/*                                                              */
/* Signature: (<CodeLinRng> C) -> CodeLinFld                    */
/*                                                              */
/****************************************************************/
intrinsic ZpResidueCode(C::CodeLinRng) -> CodeLinFld
{
Given a linear code C over Z/p^s of type (n; t1,...,ts), return the code over GF(p)
formed by taking each codeword in C modulo p. This is known as the residue code of C.

If the linear code C is over Z4, function ZpResidueCode(C) coincides with function
BinaryResidueCode(C).
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code must be over Z/p^s, with s>1";

    // since the code is linear, we only need to coerce its generator matrix to GF(p)
    return LinearCode(Matrix(GF(p), GeneratorMatrix(C)));

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: ZpTorsionCode                                 */
/* Parameters:  C, i                                            */
/* Function description: Given a linear code C over Z/p^s of    */
/*   type (n; t1,...,ts) and an integer i in {1..s}, return the */
/*   code over GF(p) formed by the vectors in {vp : p^{i-1}v in */
/*   C}, where vp is the vector v modulo p. This is a code of   */
/*   length n and dimension t1+...+ts, which is known as the    */
/*   ith torsion code of C.                                     */
/* Input parameters description:                                */
/*   - C : A linear code over Z/p^s                             */
/*   - i : An integer from {1..s}                               */
/* Output parameters description:                               */
/*   - The ith torsion code of C as a linear code over GF(p)    */
/*                                                              */
/* Function developed by Abdullah Irfan Basheer                 */
/*                                                              */
/* Signature: (<CodeLinRng> C, <RngIntElt> i) -> CodeLinFld     */
/*                                                              */
/****************************************************************/
intrinsic ZpTorsionCode(C::CodeLinRng, i::RngIntElt) -> CodeLinFld
{
Given a linear code C over Z/p^s of type (n; t1,...,ts) and an integer i in [1..s],
return the code over GF(p) formed by the vectors in [vp : p^(i-1)v in C], where vp
is the vector v modulo p. This is a code of length n and dimension t1+...+ts,
which is known as the ith torsion code of C.

If the linear code C is over Z4, function ZpTorsionCode(C, 2) coincides
with function BinaryTorsionCode(C).
}
    isOverZps, p, s := IsLinearCodeOverZps(C);
    require isOverZps and (s ge 2): "The code must be over Z/p^s, with s>1";
    requirerange i, 1, s;

    _, _, G, perm := ZpStandardForm(C);
    n := Ncols(G); // row-length of matrix
    m := Nrows(G); // column-length of matrix
    for j in [1..m] do
        if (Integers()!G[j,j] mod p^i) gt 0 then
            for k in [n..j by -1] do
                G[j,k] div:= G[j,j];
            end for;
        end if;
    end for;

    return LinearCode(Matrix(GF(p), G^(perm^(-1))));

end intrinsic;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////                  FAMILIES OF CODES OVER Z/2^s                   ////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */
/* Function name: ZpHadamardCode                                */
/* Parameters:  p, L                                            */
/* Function description: Given a prime p and a sequence  of     */
/*   nonnegative integers [t_1,...,t_s] with t_1 >= 1 and s>=2, */
/*   return a linear generalized Hadamard code over Z/p^s of    */
/*   type (n; t_1,..., t_s), where n=p^(m-s+1) and              */
/*   m=(sum_(i=1)^s(s-i+1)* t_i)-1. Moreover, return a generator*/
/*   matrix A^(t_1,...,t_s) with t_1+...+t_s rows constructed   */
/*   in a recursive way.                                        */
/* Input parameters description:                                */
/*   - p : A prime number                                       */
/*   - L : A sequence of s nonnegative integers                 */
/* Output parameters description:                               */
/*   - A linear code over Z/p^s                                 */
/*   - A generator matrix of the linear code                    */
/*                                                              */
/* Signature: (<RngIntElt> p, <[ModTupRngElt]> L) ->            */
/*                                    CodeLinRng, ModMatRngElt  */
/*                                                              */
/****************************************************************/
intrinsic ZpHadamardCode(p::RngIntElt, L::[RngIntElt]) -> CodeLinRng, ModMatRngElt
{
Given a prime p and a sequence  of nonnegative integers [t_1,...,t_s] with t_1 >= 1
and s>=2, return a linear generalized Hadamard code over Z/p^s of type (n; t_1,..., t_s),
where n=p^(m-s+1) and m=(sum_(i=1)^s(s-i+1)* t_i)-1. Moreover, return a generator
matrix A^(t_1,...,t_s) with t_1+...+t_s rows constructed in a recursive way as follows.
We start with A^(1,0,\dots,0)=(1). Then, if we have a matrix A=A^(t_1,...,t_s), for any
i in [1,...,s],
A^(t'_1,\ldots,t'_s)=    A       &     A     & ... & A
                       0*p^(i-1) & 1*p^(i-1) & ... & (p^(s-i+1)-1)*p^(i-1)
where t'_j=t_j for j<>i and t'_i=t_i+1, and p^(i-1) is the vector having the element
p^(i-1) in all its coordinates. First, we add t_1-1 rows of order p^s, up to
obtain A^(t_1,0,...,0); then t_2 rows of order p^(s-1) up to generate A^(t_1,t_2,0,...,0);
and so on, until we add t_s rows of order p to achieve A^(t_1,...,t_s).

A generalized Hadamard code over Z/p^s of length p^(m-s+1) is a code over Z/p^s such that,
after Carlet's generalized Gray map, gives a code over GF(p) (not necessarily linear) with
the same parameters as a generalized Hadamard code over GF(p) of length p^m.

If p=2 and s=2, function ZpHadamardCode(2, [t_1,t_2]) coincides with function
HadamardCodeZ4(t_1, t_2+2t_1-1).
}
    require IsPrime(p) : "Argument 1 must be a prime number";
    require L[1] ge 1 : "The first element in the sequence must be greater than or equal to 1";
    s := #L;
    require s ge 2 : "The number of elements in the sequence must be greater than o equal to 2";

    Zps := Integers(p^s);
    A := Matrix(Zps, [[1]]);

    L[1] := L[1]-1;
    for i in [1 .. s] do
        for j in [1 .. L[i]] do
            numColumns := NumberOfColumns(A);
            newRowElt := [0..p^s-1 by p^(i-1)];
            newRow := &cat[ [j^^numColumns] : j in newRowElt];
            A := VerticalJoin(HorizontalJoin([A^^#newRowElt]),
                              Matrix(Zps, [newRow]));
        end for;
    end for;

    return LinearCode(A), A;

end intrinsic;

intrinsic HadamardMatrixCodeZps(p::RngIntElt, L::[RngIntElt]) -> CodeLinRng, ModMatRngElt
{
}
    require IsPrime(p) : "Argument 1 must be a prime number";
    s := #L;
    require s ge 2 : "The number of elements in the sequence must be greater than o equal to 2";

    L[1] := L[1] + 1;
    _, A := ZpHadamardCode(p, L);
    newA := RemoveRow(A, Nrows(A));

    return LinearCode(newA), newA;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: ZpSimplexAlphaCode                            */
/* Parameters:  p, s, t                                         */
/* Function description: Given a prime p and two integers s>=2  */
/*   and t>=1, return the simplex alpha code S_t^alpha over     */
/*   Z/p^s of type (n; t, 0...0), where n=p^(st). Moreover,     */
/*   return a generator matrix G_t^alpha of S_t^alpha, which is */
/*   constructed recursively.                                   */
/* Input parameters description:                                */
/*   - p : A prime number                                       */
/*   - s : A nonnegative integer                                */
/*   - t : A nonnegative integer                                */
/* Output parameters description:                               */
/*   - A linear code over Z/p^s                                 */
/*   - A generator matrix of the linear code                    */
/*                                                              */
/* Signature: (<RngIntElt> p, <RngIntElt> s, <RngIntElt> t) ->  */
/*                               CodeLinRng, ModMatRngElt       */
/*                                                              */
/****************************************************************/
intrinsic ZpSimplexAlphaCode(p::RngIntElt, s::RngIntElt, t::RngIntElt)
                                            -> CodeLinRng, ModMatRngElt
{
Given a prime p and two integers s>=2 and t>=1, return the simplex alpha code
S_t^alpha over Z/p^s of type (n; t, 0...0), where n=p^(st). Moreover, return a
generator matrix G_t^alpha of S_t^alpha, which is constructed recursively as
follows. We start with G_1^alpha=(0 1 2 .. p^s-1). Then,
G_t^alpha =  G_(t-1)^alpha & G_(t-1)^alpha  & ... & G_(t-1)^alpha
             0             & 1              & ... & p^s-1
for t>=2, where 0,1,2,...,p^s-1 are the vectors having the elements 0,1,2,...,
p^s-1 from Z/p^s in all its coordinates, respectively.

After Carlet's generalized Gray map, Phi_s(S_t^alpha) is a simplex code over GF(p)
of type alpha, that is, a (p^(s(t+1)-1), p^(st), p^(s(t+1)-2)(p-1)) code over GF(p)
having all codewords of the same Hamming weight equal to p^(s(t+1)-2)(p-1), except
the all-zero codeword.

If p=2 and s=2, function ZpSimplexAlphaCode(2, 2, t) coincides with function
SimplexAlphaCodeZ4(t).
}
    require IsPrime(p): "Argument 1 must be a prime number";
    require s ge 2 : "Argument 2 must be greater than or equal to 2";
    require t ge 1 : "Argument 3 must be greater than or equal to 1";

    _, A := ZpHadamardCode(p, [t+1] cat [0^^(s-1)]);
    RemoveRow(~A, 1);

    return LinearCode(A), A;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: ZpSimplexBetaCode                             */
/* Parameters:  p, s, t                                         */
/* Function description: Given a prime p and two integers s>=2  */
/*   and t>=1, return the simplex beta code S_t^beta over Z/p^s */
/*   of type (n; t, 0...0), where n=p^((t-1)*(s-1))(p^t-1)/(p-1)*/
/*   Moreover, return a generator matrix G_t^beta of S_t^beta,  */
/*   which is constructed recursively.                          */
/* Input parameters description:                                */
/*   - p : A prime number                                       */
/*   - s : A nonnegative integer                                */
/*   - t : A nonnegative integer                                */
/* Output parameters description:                               */
/*   - A linear code over Z/p^s                                 */
/*   - A generator matrix of the linear code                    */
/*                                                              */
/* Signature: (<RngIntElt> p, <RngIntElt> s, <RngIntElt> t) ->  */
/*                               CodeLinRng, ModMatRngElt       */
/*                                                              */
/****************************************************************/
intrinsic ZpSimplexBetaCode(p::RngIntElt, s::RngIntElt, t::RngIntElt)
                                              -> CodeLinRng, ModMatRngElt
{
Given a prime p and two integers s>=2 and t>=1, return the simplex beta code
S_t^beta over Z/p^s of type (n; t, 0...0), where n=p^((t-1)*(s-1))(p^t-1)/(p-1).
Moreover, return a generator matrix G_t^beta of S_t^beta, which is constructed
recursively as follows. We start with G_1^beta=(1). Then,
G_t^beta = G_(t-1)^alpha &   G_(t-1)^beta & G_(t-1)^beta  & ... & G_(t-1)^beta
            1            &   0            & p             & ... & p^s-p
for t>=2, where 1,0,p,...,p^s-2 are the vectors having the elements 1,0,p,...,
p^s-p from Z/p^s in all its coordinates, respectively.

After Carlet's generalized Gray map, Phi_s(S_t^beta) is a simplex code over GF(p)
of type beta, that is, a (p^(st-t)(p^t-1)/(p-1), p^(st), p^(st-t-1)(p^t-1)) code
over GF(p) with p^t(p^((s-1)t)-1) codewords of Hamming weight p^(st-t-1)(p^t-1),
p^t-1 codewords of Hamming weight p^(st-1), and the all-zero codeword.

If p=2 and s=2, function ZpSimplexBetaCode(2, 2, t) may not coincide with function
SimplexBetaCodeZ4(t), but the obtained codes are monomially equivalent (one can
be obtained from the other by permuting coordinates and, if necessary, changing
the sign of certain coordinates).
}
    require IsPrime(p): "Argument 1 must be a prime number";
    require s ge 2 : "Argument 2 must be greater than or equal to 2";
    require t ge 1 : "Argument 3 must be greater than or equal to 1";

    Zps := Integers(p^s);
    if (t eq 1) then
        A := Matrix(Zps, [[1]]);
    else
        _, AHadamard := ZpHadamardCode(p, [t] cat [0^^(s-1)]);
        SwapRows(~AHadamard, 1, Nrows(AHadamard));
        _, ASimplexBeta := ZpSimplexBetaCode(p, s, t-1);
        nSimplexBeta := Ncols(ASimplexBeta);
        seqMatrices := <>;
        for i in [0..p^(s-1)-1] do
            Append(~seqMatrices,
                   VerticalJoin(ASimplexBeta, Matrix(Zps, [[(p*i)^^nSimplexBeta]]) ));
        end for;
        A := HorizontalJoin(AHadamard, HorizontalJoin(seqMatrices));
    end if;

    return LinearCode(A), A;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: ZpMacDonaldAlphaCode                          */
/* Parameters:  p, s, t, u                                      */
/* Function description: Given a prime p and three              */
/*   integers s>=2, t>=1, and 1<=u<t, return the MacDonald      */
/*   alpha code M_(t,u)^alpha over Z/p^s of type (n;t,0,...,0). */
/*   Moreover, return a generator matrix G_(t,u)^alpha of       */
/*   M_(t,u)^alpha, constructed from a generator matrix         */
/*   G_t^alpha of the simplex alpha code over Z/p^s.            */
/* Input parameters description:                                */
/*   - p : A prime number                                       */
/*   - t : A nonnegative integer                                */
/*   - s : A nonnegative integer                                */
/*   - u : A nonnegative integer 1 <= u < t                     */
/* Output parameters description:                               */
/*   - A linear code over Z/p^s                                 */
/*   - A generator matrix of the linear code                    */
/*                                                              */
/* Signature:(<RngIntElt> p, <RngIntElt> t, <RngIntElt> s,      */
/*            <RngIntElt> u) -> CodeLinRng, ModMatRngElt        */
/*                                                              */
/****************************************************************/
intrinsic ZpMacDonaldAlphaCode(p::RngIntElt, s::RngIntElt, t::RngIntElt, u::RngIntElt)
                                -> CodeLinRng, ModMatRngElt
{
Given a prime p and three integers s>=2, t>=1, and 1<=u<t, return the MacDonald
alpha code M_(t,u)^alpha over Z/p^s of type (n;t,0,...,0). Moreover, return a
generator matrix G_(t,u)^alpha of M_(t,u)^alpha, constructed from a generator
matrix G_t^alpha of the simplex alpha code over Z/p^s as follows:
G_(t,u)^alpha= ( G_t^alpha \ [G_u^alpha / 0] )
where (A \ B) denotes the matrix obtained from the matrix A by deleting the columns
of the matrix B, and 0 is the (t-u) x p^(su) zero matrix.

After Carlet's generalized Gray map, Phi_s(M_(t,u)^alpha) is a
(p^(s(t+1)-1)-p^(s(u+1)-1), p^(st)) MacDonald code over GF(p) of type alpha.
}
    require IsPrime(p): "Argument 1 must be a prime number";
    require s ge 2 : "Argument 2 must be greater than or equal to 2";
    require t ge 2 : "Argument 3 must be greater than or equal to 2";
    requirerange u, 1, t-1;

    _, ASimplex := ZpSimplexAlphaCode(p, s, t);
    A := ColumnSubmatrixRange(ASimplex, (p^(s*u)) + 1, (p^(s*t)));

    return LinearCode(A), A;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: ZpMacDonaldBetaCode                           */
/* Parameters:  p, s, t, u                                      */
/* Function description: Given a prime p and three              */
/*   integers s>=2, t>=1, and 1<=u<t, return the MacDonald      */
/*   beta code M_(t,u)^beta over Z/p^s of type (n;t,0,...,0).   */
/*   Moreover, return a generator matrix G_(t,u)^beta of        */
/*   M_(t,u)^beta, constructed from a generator matrix          */
/*   G_t^beta of the simplex alpha code over Z/p^s.             */
/* Input parameters description:                                */
/*   - p : A prime number                                       */
/*   - t : A nonnegative integer                                */
/*   - s : A nonnegative integer                                */
/*   - u : A nonnegative integer 1 <= u < t                     */
/* Output parameters description:                               */
/*   - A linear code over Z/p^s                                 */
/*   - A generator matrix of the linear code                    */
/*                                                              */
/* Signature:(<RngIntElt> p, <RngIntElt> t, <RngIntElt> s,      */
/*            <RngIntElt> u) -> CodeLinRng, ModMatRngElt        */
/*                                                              */
/****************************************************************/
intrinsic ZpMacDonaldBetaCode(p::RngIntElt, s::RngIntElt, t::RngIntElt, u::RngIntElt)
                               -> CodeLinRng, ModMatRngElt
{
Given a prime p and three integers s>=2, t>=1, and 1<=u<t, return the MacDonald
beta code M_(t,u)^beta over Z/p^s of type (n;t,0,...,0). Moreover, return a
generator matrix G_(t,u)^beta of M_(t,u)^beta, constructed from a generator
matrix G_t^beta of the simplex beta code over Z/p^s as follows:
G_(t,u)^beta = ( G_t^beta \ [G_u^beta / 0] )
where (A \ B) denotes the matrix obtained from the matrix A by deleting the
columns of the matrix B, and 0 is a zero matrix.

After Carlet's generalized Gray map, Phi_s(M_(t,u)^beta) is a
(p^(st-t)(p^t-1)/(p-1)-p^(su-u)(p^u-1)/(p-1), p^(st)) MacDonald code over GF(p)
of type beta.
}
    require IsPrime(p): "Argument 1 must be a prime number";
    require s ge 2 : "Argument 2 must be greater than or equal to 2";
    require t ge 2 : "Argument 3 must be greater than or equal to 2";
    requirerange u, 1, t-1;

    _, ASimplex := ZpSimplexBetaCode(p, s, t);
    numColSimplexU := Integers()!(p^(s*u-u-s+1)*(p^u-1)/(p-1));
    numI := &+[p^(s*(t-i)) : i in [1..(t-u)]];
    A1 := ColumnSubmatrixRange(ASimplex, 1, numI);
    A2 := ColumnSubmatrixRange(ASimplex, numI + numColSimplexU + 1, Ncols(ASimplex));
    A := HorizontalJoin(A1, A2);

    return LinearCode(A), A;

end intrinsic;
