///////////////////////////////////////////////////////////////////////////////
/////////       Copyright 2024 Mercè Villanueva                         ///////
/////////                                                               ///////
/////////       This program is distributed under the terms of GNU      ///////
/////////               General Public License                          ///////
/////////                                                               ///////
///////////////////////////////////////////////////////////////////////////////

/******************************************************************************
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
******************************************************************************/


/*************************************************************/
/*								                             */
/* Project name: ZpZp^2..Z/p^s-additive codes in MAGMA	     */
/* File name: MixZpAdditiveCodes_Core.m				         */
/*								                             */
/* Comment: Package developed within the CCSG group      	 */
/*								                             */
/* Authors: Mercè Villanueva, Hui Hong Wu, and Adrián Torres */
/*                                                           */
/* Revision version and last date: v1.0   13-08-2019		 */
/*                                 v1.1   04-06-2021         */
/*        new type MixZpCode       v2.0   20-08-2024         */
/*                                 v3.0   17-01-2025         */
/*                                 v3.1   13-02-2026         */
/*                                                           */
/*************************************************************/
//Uncomment freeze when package finished
//freeze;

intrinsic MixZpAdditiveCodes_Core_version() -> SeqEnum
{Return the current version of this file.}

    version := [3, 1];
    return version;

end intrinsic;

//////  Functions we need from the ZpsAdditiveCode package

import "ZpAdditiveCodes_Core.m": IsLinearCodeOverZps,
                                 IsMatrixOverZps;

//////  Type declaration

declare type MixZpCode;

declare attributes MixZpCode:
    LengthSeq,            //a sequence with the length of each part over Z/p^i
    BaseRing,             //the base ring Zp, p prime
    Code,                 //the corresponding code over Z/p^s
    Type,                 //a sequence with the values t1,..,ts of the code
    ExtendType,           //an s x s matrix with the extend type K of the code
    MinimumHomWeight,     //minimum homogeneous weight of the code
    MinimumHomWeightLowerBound,    //minimum homogeneous weight lower bound
    MinimumHomWeightUpperBound,    //minimum homogeneous weight upper bound
    MinimumHomWeightWord,   //a codeword of minimum homogeneous weight
    HomWeightDistribution;  //the homogeneous weight distribution

/******************************************************************************
                            Checks
******************************************************************************/

over_Z4 := func<C | Alphabet(C) cmpeq Integers(4)>;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////						CONVERSION FUNCTIONS		    			///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/******************************************************************************
		        Conversion functions from/to Z/p^s to/from Zp
******************************************************************************/

// M is a matrix over Z/p^s, where the first coordinates are multiplied by
// powers of p.
procedure MixZpChangeMatrixZptoZps(~M, p, lengthSeq);
    lowerInterval := 1;
    s := #lengthSeq;
    for i in [1..s-1] do
        upperInterval := lowerInterval + lengthSeq[i] -1;
        for alpha in [lowerInterval..upperInterval] do
            MultiplyColumn(~M, p^(s-i), alpha);
        end for;
        lowerInterval := upperInterval + 1;
    end for;
end procedure;

// M is a matrix over Z/ps, where the coordinates which are multiples of
// powers of p, are divided by these powers of p.
procedure MixZpChangeMatrixZpstoZp(~M, p, lengthSeq);
    lowerInterval := 1;
    s := #lengthSeq;
    for i in [1..s-1] do
        upperInterval := lowerInterval + lengthSeq[i] -1;
        for alpha in [lowerInterval..upperInterval] do
            for j in [1..Nrows(M)] do
                M[j, alpha] := M[j, alpha] div p^(s-i);
            end for;
        end for;
        lowerInterval := upperInterval + 1;
    end for;
end procedure;

/*****************************************************************************/
/*                                                                           */
/* Function name: IsMixZpAdditiveCodeOverZps                                 */
/* Parameters: M, p, lengthSeq                                               */
/* Function description: Given a matrix M over Z/p^s, the prime number p,    */
/*   and a sequence of non-negative integers lengthSeq, check whether the    */
/*   elements in the columns of X_i are multiples of p^i or not.             */
/* Input parameters description:                                             */
/*   - M: A matrix over Z/p^s                                                */
/*   - p: The prime number p                                                 */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The partition of [1..a_1+..+a_s] into the sequences X1,..,Xs          */
/*                                                                           */
/*****************************************************************************/
function IsMixZpAdditiveOverZps(M, p, lengthSeq)
    Mt := Transpose(M);
    lowerInterval := 1;
    s := #lengthSeq;
    for i in [1..s-1] do
        upperInterval := lowerInterval + lengthSeq[i] -1;
        for alpha in [lowerInterval..upperInterval] do
            if not IsZero(p^i * Mt[alpha]) then
                return false;
            end if;
        end for;
        lowerInterval := upperInterval + 1;
    end for;
    return true;
end function;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpCoordinatesPartition                                  */
/* Parameters: lengthSeq                                                     */
/* Function description: Given a sequence of non-negative integers lengthSeq,*/
/*   return the partition of the coordinate positions [1..a_1+...+a_s] into  */
/*   s sequences of size a_1, ..., a_s having consecutive elements, that is, */
/*   X1 = {1,..,a_1}, X2 = {a_1+1,..,a_1+a_2}, and so on until Xs =          */
/*   {a_1+..+a_s-1+1,..,a_1+..+a_s}.                                         */
/* Input parameters description:                                             */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The partition of [1..a_1+..+a_s] into the sequences X1,..,Xs          */
/*                                                                           */
/*****************************************************************************/
function MixZpCoordinatesPartition(lengthSeq)
    Lseq := [];
    lowerInterval := 1;
    s := #lengthSeq;
    for i in [1..s] do
        upperInterval := lowerInterval + lengthSeq[i] - 1;
        Append(~Lseq, [lowerInterval..upperInterval]);
        lowerInterval := upperInterval + 1;
    end for;
    return Lseq;
end function;

/*****************************************************************************/
/*                                                                           */
/* Function name: FromZpstoMixZp                                             */
/* Parameters: u, lengthSeq                                                  */
/* Function description: Given a vector u over Z/p^s of length a_1+...+a_s   */
/*   and a sequence of non-negative integers lengthSeq = [a_1,...,a_s],return*/
/*   the conversion of this vector to a tuple in the cartesian product set   */
/*   Zp^a_1 x (Zp^2)^a_2 x .. x (Zp^s)^a_s, replacing the elements jp^(s-i)  */
/*   over Z/p^s in the coordinates in X_i to j over Z/p^i for i in [1,..,s]. */
/*   It is checked whether the elements in the coordinates in X_i belong to  */
/*   the set [ 0, p^(s-i), 2p^(s-i),..,(p^i-1)p^(s-i) ].                     */
/* Input parameters description:                                             */
/*   - u: A vector over Z/p^s                                                */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The tuple representing the vector u in the cartesian product set      */
/*     Zp^a_1 x (Zp^2)^a_2 x .. x (Zp^s)^a_s                                 */
/*                                                                           */
/* Signature: (<ModTupRngElt> u, <SeqEnum> lengthSeq) -> Tup                 */
/*                                                                           */
/*****************************************************************************/
intrinsic FromZpstoMixZp(u::ModTupRngElt, lengthSeq::[RngIntElt]) -> Tup
{
Given a vector u over Z/p^s of length a_1+...+a_s and a sequence of non-negative
integers lengthSeq = [a_1,...,a_s], return the conversion of this vector to a tuple
in the cartesian product set Zp^a_1 x (Zp^2)^a_2 x .. x (Zp^s)^a_s, replacing the
elements jp^(s-i) over Z/p^s in the coordinates in X_i to j over Z/p^i for i in
[1,..,s]. It is checked whether the elements in the coordinates in X_i belong to
the set [ 0, p^(s-i), 2p^(s-i),..,(p^i-1)p^(s-i) ].
}
    require Min(lengthSeq) ge 0: "Argument 2 must be a sequence of non-negative integers";
    n := OverDimension(u);
    require &+lengthSeq eq n: "Argument 2 is not compatible with the length of the vector";
    M := Matrix(u);
    isOverZps, p, s := IsMatrixOverZps(M);
    require isOverZps and (s ge 2): "The vector must be over Z/p^s with s>0";
    require IsMixZpAdditiveOverZps(M, p, lengthSeq):
            "Coordinates must be multiples of powers of p according to argument 3";

    MixZpChangeMatrixZpstoZp(~M, p, lengthSeq);
    Lseq := MixZpCoordinatesPartition(lengthSeq);
    return <Vector(Integers(p^k), [M[1][j] : j in Lseq[k] ] ) : k in [1..#Lseq] >;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: FromZpstoMixZp                                             */
/* Parameters: L, lengthSeq                                                  */
/* Function description: Given a sequence L of vectors over Z/p^s of length  */
/*   a_1+...+a_s and a sequence of non-negative integers lengthSeq = [a_1,..,*/
/*   a_s], return the conversion of these vectors to a sequence of tuples in */
/*   the cartesian product set Zp^a_1 x (Zp^2)^a_2 x .. x (Zp^s)^a_s,        */
/*   replacing the elements jp^(s-i) over Z/p^s in the coordinates in X_i to */
/*   j over Z/p^i for i in [1,..,s]. It is checked whether the elements in   */
/*   the coordinates in X_i belong to the set [ 0, p^(s-i), 2p^(s-i),..,     */
/*   (p^i-1)p^(s-i) ].                                                       */
/* Input parameters description:                                             */
/*   - L: A sequence of vectors over Z/p^s                                   */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - A sequence of tuples in the cartesian product set                     */
/*     Zp^a_1 x (Zp^2)^a_2 x .. x (Zp^s)^a_s                                 */
/*                                                                           */
/* Signature: (<SeqEnum[ModTupRngElt]> L, <SeqEnum> lengthSeq) -> SeqEnum    */
/*                                                                           */
/*****************************************************************************/
intrinsic FromZpstoMixZp(L::SeqEnum[ModTupRngElt], lengthSeq::[RngIntElt]) -> SeqEnum
{
Given a sequence L of vectors over Z/p^s of length a_1+...+a_s and a sequence of
non-negative integers lengthSeq = [a_1,...,a_s], return the conversion of these
vectors to a sequence of tuples in the cartesian product set Zp^a_1 x (Zp^2)^a_2
x .. x (Zp^s)^a_s, replacing the elements jp^(s-i) over Z/p^s in the coordinates
in X_i to j over Z/p^i for i in [1,..,s]. It is checked whether the elements in
the coordinates in X_i belong to the set [ 0, p^(s-i), 2p^(s-i),..,(p^i-1)p^(s-i) ].
}
    require not(IsEmpty(L)): "Argument 1 cannot be empty";
    //require ElementType(L) eq ModTupRngElt:
    //        "Argument 1 does not contain vectors over Z/p^s";
    require Min(lengthSeq) ge 0: "Argument 2 must be a sequence of non-negative integers";
    n := OverDimension(L[1]);
    require &+lengthSeq eq n: "Argument 2 is not compatible with the length of the vectors";
    M := Matrix(L);
    isOverZps, p, s := IsMatrixOverZps(M);
    require isOverZps and (s ge 2): "The vectors must be over Z/p^s with s>0";
    require IsMixZpAdditiveOverZps(M, p, lengthSeq):
            "Coordinates must be multiples of powers of p according to argument 3";

    MixZpChangeMatrixZpstoZp(~M, p, lengthSeq);
    Lseq := MixZpCoordinatesPartition(lengthSeq);
    return [ <Vector(Integers(p^k), [M[i][j] : j in Lseq[k] ] ) : k in [1..#Lseq] >
                                                              : i in [1..Nrows(M)] ];
end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: FromZpstoMixZp                                             */
/* Parameters: S, lengthSeq                                                  */
/* Function description: Given a set S of vectors over Z/p^s of length       */
/*   a_1+...+a_s and a sequence of non-negative integers lengthSeq = [a_1,..,*/
/*   a_s], return the conversion of these vectors to a set of tuples in      */
/*   the cartesian product set Zp^a_1 x (Zp^2)^a_2 x .. x (Zp^s)^a_s,        */
/*   replacing the elements jp^(s-i) over Z/p^s in the coordinates in X_i to */
/*   j over Z/p^i for i in [1,..,s]. It is checked whether the elements in   */
/*   the coordinates in X_i belong to the set [ 0, p^(s-i), 2p^(s-i),..,     */
/*   (p^i-1)p^(s-i) ].                                                       */
/* Input parameters description:                                             */
/*   - S: A set of vectors over Z/p^s                                        */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - A set of tuples in the cartesian product set                          */
/*     Zp^a_1 x (Zp^2)^a_2 x .. x (Zp^s)^a_s                                 */
/*                                                                           */
/* Signature: (<SetEnum[ModTupRngElt]> S, <SeqEnum> lengthSeq) -> SetEnum    */
/*                                                                           */
/*****************************************************************************/
intrinsic FromZpstoMixZp(S::SetEnum[ModTupRngElt], lengthSeq::[RngIntElt]) -> SetEnum
{
Given a set S of vectors over Z/p^s of length a_1+...+a_s and a sequence of
non-negative integers lengthSeq = [a_1,...,a_s], return the conversion of these
vectors to a set of tuples in the cartesian product set Zp^a_1 x (Zp^2)^a_2
x .. x (Zp^s)^a_s, replacing the elements jp^(s-i) over Z/p^s in the coordinates
in X_i to j over Z/p^i for i in [1,..,s]. It is checked whether the elements in
the coordinates in X_i belong to the set [ 0, p^(s-i), 2p^(s-i),..,(p^i-1)p^(s-i) ].
}
    require not(IsEmpty(S)): "Argument 1 cannot be empty";
    //require ElementType(S) eq ModTupRngElt:
    //        "Argument 1 does not contain vectors over Z/p^s";
    require Min(lengthSeq) ge 0: "Argument 2 must be a sequence of non-negative integers";
    S := Setseq(S);
    n := OverDimension(S[1]);
    require &+lengthSeq eq n: "Argument 2 is not compatible with the length of the vectors";
    M := Matrix(S);
    isOverZps, p, s := IsMatrixOverZps(M);
    require isOverZps and (s ge 2): "The vectors must be over Z/p^s with s>0";
    require IsMixZpAdditiveOverZps(M, p, lengthSeq):
            "Coordinates must be multiples of powers of p according to argument 3";

    MixZpChangeMatrixZpstoZp(~M, p, lengthSeq);
    Lseq := MixZpCoordinatesPartition(lengthSeq);
    return { <Vector(Integers(p^k), [M[i][j] : j in Lseq[k] ] ) : k in [1..#Lseq] >
                                                              : i in [1..Nrows(M)] };
end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: FromZpstoMixZp                                             */
/* Parameters: M, lengthSeq                                                  */
/* Function description: Given a matrix M over Z/p^s with a_1+...+a_s columns*/
/*   and a sequence of non-negative integers lengthSeq = [a_1,..,a_s], return*/
/*   the conversion of the sequence with the rows of M to a sequence of      */
/*   tuples in the cartesian product set Zp^a_1 x (Zp^2)^a_2 x..x (Zp^s)^a_s,*/
/*   replacing the elements jp^(s-i) over Z/p^s in the coordinates in X_i to */
/*   j over Z/p^i for i in [1,..,s]. It is checked whether the elements in   */
/*   the coordinates in X_i belong to the set [ 0, p^(s-i), 2p^(s-i),..,     */
/*   (p^i-1)p^(s-i) ].                                                       */
/* Input parameters description:                                             */
/*   - M: A matrix over Zps with a_1+...+a_s columns                         */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - A sequence of tuples in the cartesian product set                     */
/*     Zp^a_1 x (Zp^2)^a_2 x .. x (Zp^s)^a_s                                 */
/*                                                                           */
/* Signature: (<ModMatRngElt> M, <SeqEnum> lengthSeq) -> SeqEnum             */
/*                                                                           */
/*****************************************************************************/
intrinsic FromZpstoMixZp(M::ModMatRngElt, lengthSeq::[RngIntElt]) -> SeqEnum
{
Given a matrix M over Z/p^s with a_1+...+a_s columns and a sequence of non-negative
integers lengthSeq = [a_1,...,a_s], return the conversion of the sequence with the
rows of M to a sequence of tuples in the cartesian product set Zp^a_1 x (Zp^2)^a_2
x .. x (Zp^s)^a_s, replacing the elements jp^(s-i) over Z/p^s in the coordinates
in X_i to j over Z/p^i for i in [1,..,s]. It is checked whether the elements in
the coordinates in X_i belong to the set [ 0, p^(s-i), 2p^(s-i),..,(p^i-1)p^(s-i) ].
}
    n := Ncols(M);
    require (n gt 0): "Argument 1 cannot be a matrix with 0 columns";
    require Min(lengthSeq) ge 0: "Argument 2 must be a sequence of non-negative integers";
    require &+lengthSeq eq n: "Argument 2 is not compatible with the length of the vectors";
    isOverZps, p, s := IsMatrixOverZps(M);
    require isOverZps and (s ge 2): "The vectors must be over Z/p^s with s>0";
    require IsMixZpAdditiveOverZps(M, p, lengthSeq):
            "Coordinates must be multiples of powers of p according to argument 3";

    MixZpChangeMatrixZpstoZp(~M, p, lengthSeq);
    Lseq := MixZpCoordinatesPartition(lengthSeq);
    return [ <Vector(Integers(p^k), [M[i][j] : j in Lseq[k] ] ) : k in [1..#Lseq] >
                                                              : i in [1..Nrows(M)] ];
end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: FromZpstoMixZp                                             */
/* Parameters: M, lengthSeq                                                  */
/* Function description: Given a matrix M over Z/p^s with a_1+...+a_s columns*/
/*   and a sequence of non-negative integers lengthSeq = [a_1,..,a_s], return*/
/*   the conversion of the sequence with the rows of M to a sequence of      */
/*   tuples in the cartesian product set Zp^a_1 x (Zp^2)^a_2 x..x (Zp^s)^a_s,*/
/*   replacing the elements jp^(s-i) over Z/p^s in the coordinates in X_i to */
/*   j over Z/p^i for i in [1,..,s]. It is checked whether the elements in   */
/*   the coordinates in X_i belong to the set [ 0, p^(s-i), 2p^(s-i),..,     */
/*   (p^i-1)p^(s-i) ].                                                       */
/* Input parameters description:                                             */
/*   - M: A matrix over Zps with a_1+...+a_s columns                         */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - A sequence of tuples in the cartesian product set                     */
/*     Zp^a_1 x (Zp^2)^a_2 x .. x (Zp^s)^a_s                                 */
/*                                                                           */
/* Signature: (<AlgMatElt> M, <SeqEnum> lengthSeq) -> SeqEnum                */
/*                                                                           */
/*****************************************************************************/
intrinsic FromZpstoMixZp(M::AlgMatElt, lengthSeq::[RngIntElt]) -> SeqEnum
{
Given a matrix M over Z/p^s with a_1+...+a_s columns and a sequence of non-negative
integers lengthSeq = [a_1,...,a_s], return the conversion of the sequence with the
rows of M to a sequence of tuples in the cartesian product set Zp^a_1 x (Zp^2)^a_2
x .. x (Zp^s)^a_s, replacing the elements jp^(s-i) over Z/p^s in the coordinates
in X_i to j over Z/p^i for i in [1,..,s]. It is checked whether the elements in
the coordinates in X_i belong to the set [ 0, p^(s-i), 2p^(s-i),..,(p^i-1)p^(s-i) ].
}
    n := Ncols(M);
    require (n gt 0): "Argument 1 cannot be a matrix with 0 columns";
    require Min(lengthSeq) ge 0: "Argument 2 must be a sequence of non-negative integers";
    require &+lengthSeq eq n: "Argument 2 is not compatible with the length of the vectors";
    isOverZps, p, s := IsMatrixOverZps(M);
    require isOverZps and (s ge 2): "The vectors must be over Z/p^s with s>0";
    require IsMixZpAdditiveOverZps(M, p, lengthSeq):
            "Coordinates must be multiples of powers of p according to argument 3";

    MixZpChangeMatrixZpstoZp(~M, p, lengthSeq);
    Lseq := MixZpCoordinatesPartition(lengthSeq);
    return [ <Vector(Integers(p^k), [M[i][j] : j in Lseq[k] ] ) : k in [1..#Lseq] >
                                                              : i in [1..Nrows(M)] ];
end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: FromMixZptoZps                                             */
/* Parameters: u, p                                                          */
/* Function description: Given a tuple u in the cartesian product set Zp^a_1 */
/*   x(Zp^2)^a_2 x...x (Zp^s)^a_s and a prime number p, return the conversion*/
/*   of the tuple u to a vector over Z/p^s of length a_1+...+a_s with its a_i*/
/*   coordinates in positions X_i=[a_1+...+a_(i-1)+1, ..., a_1+...+a_i]      */
/*   multiplied by p^(s-i) for i in [1,..,s].                                */
/* Input parameters description:                                             */
/*   - u: A tuple u of size s, where each component u[i] lies in Z/p^i       */
/*   - p: A prime integer specifying the modular base                        */
/* Output parameters description:                                            */
/*   - The vector over Z/p^s representing the tuple u                        */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<Tup> u, <RngIntElt> p) -> ModTupRngElt                       */
/*                                                                           */
/*****************************************************************************/
intrinsic FromMixZptoZps(u::Tup, p::RngIntElt) -> ModTupRngElt
{
Given a tuple u in the cartesian product set Zp^a_1 x (Zp^2)^a_2 x...x (Zp^s)^a_s
and a prime number p, return the conversion of the tuple u to a vector over
Z/p^s of length a_1+...+a_s with its a_i coordinates in positions
X_i=[a_1+...+a_(i-1)+1, ..., a_1+...+a_i] multiplied by p^(s-i) for i in [1,..,s].
}
    s := #u;
    for i in [1..s] do
        require Type(u[i]) cmpeq ModTupRngElt:
            "Argument 1 must be a tuple containing vectors over a ring";
        require BaseRing(u[i]) cmpeq Integers(p^i):
            "The i-th component vector in the tuple must be over the ring Z/p^i";
    end for;
    require IsPrime(p): "Argument 2 must be a prime number";

    Zps := Integers(p^s);
    return HorizontalJoin(<ChangeRing(u[i], Zps) * p^(s - i) : i in [1..s]>)[1];

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: FromMixZptoZps                                             */
/* Parameters: L, p                                                          */
/* Function description: Given a sequence L of tuples in the cartesian       */
/*   product set Zp^a_1 x (Zp^2)^a_2 x...x (Zp^s)^a_s and a prime number p,  */
/*   return the conversion of theses tuples to a sequence of vectors over    */
/*   Z/p^s of length a_1+...+a_s with their a_i coordinates in positions     */
/*   X_i=[a_1+...+a_(i-1)+1, ..., a_1+...+a_i] multiplied by p^(s-i) for     */
/*   i in [1,..,s].                                                          */
/* Input parameters description:                                             */
/*   - L: A sequence of tuples of size s, where each component u[i] lies in  */
/*        Z/p^i for every tuple u in L                                       */
/*   - p: A prime integer specifying the modular base                        */
/* Output parameters description:                                            */
/*   - A sequence of vectors over Z/p^s representing the sequence of tuples  */
/*                                                                           */
/* Function developed by Merce Villanueva                                    */
/*                                                                           */
/* Signature: (<SeqEnum[Tup]> L, <RngIntElt> p) -> [ModTupRngElt]            */
/*                                                                           */
/*****************************************************************************/
intrinsic FromMixZptoZps(L::SeqEnum[Tup], p::RngIntElt) -> SeqEnum
{
Given a sequence L of tuples in the cartesian product set Zp^a_1 x (Zp^2)^a_2 x
...x (Zp^s)^a_s and a prime number p, return the conversion of theses tuples to
a sequence of vectors over Z/p^s of length a_1+...+a_s with their a_i coordinates
in positions X_i=[a_1+...+a_(i-1)+1, ..., a_1+...+a_i] multiplied by p^(s-i)
for i in [1,..,s].
}
    u := L[1]; // the first tuple in L
    s := #u;
    for i in [1..s] do
        require Type(u[i]) cmpeq ModTupRngElt:
            "Argument 1 must be a sequence of tuples containing vectors over a ring";
        require BaseRing(u[i]) cmpeq Integers(p^i):
            "The i-th component vector in each tuple must be over the ring Z/p^i";
    end for;
    require IsPrime(p): "Argument 2 must be a prime number";

    Zps := Integers(p^s);
    newL := [];
    for u in L do
        Append(~newL, HorizontalJoin(<ChangeRing(u[i], Zps) * p^(s-i) : i in [1..s]>)[1]);
    end for;

    return newL;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////            USER DEFINED TYPE: PRINTING                          ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Procedure name: Print                                                     */
/* Parameters: C, L                                                          */
/* Procedure description: Given a ZpZp^2..Zp^s-additive code C, print the    */
/*   information associated to the code C. The procedure is called automati- */
/*   cally by Magma whenever the object C is to be printed.                  */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/*   - L: "Default", "Minimal", "Maximal", "Magma"                           */
/*                                                                           */
/* Signature: (<MixZpCode> C, <MonStgElt> L)                                 */
/*                                                                           */
/*****************************************************************************/
intrinsic Print(C::MixZpCode, L::MonStgElt)
{
Print the ZpZp^2..Zp^s-additive code C information at level L.
}
    cardinalCode := #C;
    typeC := Reverse(ZpType(C`Code));
    lengthC := Length(C`Code);

    case L:
        when "Default" :
            //N, M, d Z2Z4Code
            if assigned C`MinimumHomWeight then
                printf "(%o, %o, %o) ZpZp^2..Zp^s-additive code of length %o and type %o\n",
                        lengthC, cardinalCode, C`MinimumHomWeight, C`LengthSeq, typeC;
            else
                printf "(%o, %o) ZpZp^2..Zp^s-additive code of length %o and type %o\n",
                        lengthC, cardinalCode, C`LengthSeq, typeC;
            end if;
            printf "Generator matrix:\n%o", GeneratorMatrix(C`Code);
        when "Minimal" :
            //N, M, d MixZpCode
            if assigned C`MinimumHomWeight then
                printf "(%o, %o, %o) ZpZp^2..Zp^s-additive code of length %o and type %o",
                        lengthC, cardinalCode, C`MinimumHomWeight, C`LengthSeq, typeC;
            else
                printf "(%o, %o) ZpZp^2..Zp^s-additive code of length %o and type %o",
                        lengthC, cardinalCode, C`LengthSeq, typeC;
            end if;
        when "Maximal" :
            //N, M, d MixZpCode
            if assigned C`MinimumHomWeight then
                printf "(%o, %o, %o) ZpZp^2..Zp^s-additive code of length %o and type %o\n",
                        lengthC, cardinalCode, C`MinimumHomWeight, C`LengthSeq, typeC;
                if assigned C`CoveringRadius then
                    printf "having a (%o, %o, %o) code over Zp as its Gray map image,
                            with covering radius %o\n",
                        MixZpLengthOverZp(C), cardinalCode, C`MinimumHomWeight, C`CoveringRadius;
                else
                    printf "having a (%o, %o, %o) code over Zp as its Gray map image \n",
                        MixZpLengthOverZp(C), cardinalCode, C`MinimumHomWeight;
                end if;
            else
                printf "(%o, %o) ZpZp^2..Zp^s-additive code of length %o and type %o\n",
                        lengthC, cardinalCode, C`LengthSeq, typeC;
                printf "having a (%o, %o) code over Zp as its Gray map image \n",
                        MixZpLengthOverZp(C), cardinalCode;
            end if;
            printf "Generator matrix:\n%o", GeneratorMatrix(C`Code);
        when "Magma" :
            p := #(C`BaseRing);
            printf "MixZpAdditiveCode(%O, %o, %O)", GeneratorMatrix(C`Code), "Magma", p,
                                          C`LengthSeq, "Magma";
    end case;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////            USER DEFINED TYPE: PARENT                            ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//non needed
//intrinsic Parent(C::MixZpCode) -> .
//end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////            USER DEFINED TYPE: COERCION                          ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: IsMemberOf                                                 */
/* Parameters: u, C                                                          */
/* Function description: Given a vector u over Z/p^s such that it has some   */
/*   coordinates from {0..p-1}, some form {0..p^2-1}, and so on until some   */
/*   over Zp^s, and a ZpZp^2..Zp^s-additive code C, return true if u is in   */
/*   the code C and false otherwise.                                         */
/* Input parameters description:                                             */
/*   - u: A vector over Z/p^s                                                */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - true if u is in C, and false otherwise                                */
/*                                                                           */
/*****************************************************************************/
function IsMemberOf(u, C)
    p := #C`BaseRing;
    s := #C`LengthSeq;
    RZps := RSpace(Integers(p^s), Length(C`Code));
    if Parent(u) cmpeq RZps then
        Mu := Matrix(u);
        if not IsMixZpAdditiveOverZps(Mu, p, C`LengthSeq) then
            MixZpChangeMatrixZptoZps(~Mu, p, C`LengthSeq);
        end if;
        return Mu[1] in C`Code;
    else
        //case u is not coercible to RZps
        return false;
    end if;
end function;

/*****************************************************************************/
/*                                                                           */
/* Function name: IsCoercible                                                */
/* Parameters: C, c                                                          */
/* Function description: Given a ZpZp^2..Zp^s-additive code C, and an object */
/*   c of any type, return whether c is coercible into C and the coerced     */
/*   element if c is coercible to C.                                         */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/*   - c: An object of any type                                              */
/* Output parameters description:                                            */
/*   - true if c is coercible to C, and false otherwise                      */
/*   - the object c coerced to C, if c is coercible to C                     */
/*                                                                           */
/* Signature: (<MixZpCode> C, <.> c) -> BoolElt, .                           */
/*                                                                           */
/*****************************************************************************/
intrinsic IsCoercible(C::MixZpCode, c::.) -> BoolElt, .
{
Return whether c is coercible into C and the result if so.
}
    p := #C`BaseRing;
    s := #C`LengthSeq;
    RZps := RSpace(Integers(p^s), Length(C`Code));
    isCoercible, v := IsCoercible(RZps, c);
    if isCoercible then
        if IsMemberOf(v, C) then
            return true, v;
        else
            return false, "Illegal coercion";
        end if;
    else
        return false, "Illegal coercion";
    end if;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////        CONSTRUCTION OF GENERAL ZpZp^2..Zp^s-ADDITIVE CODES      ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: NewCodeMixZp                                               */
/* Parameters: code, p, lengthSeq                                            */
/* Function description: Create a new ZpZp^2..Z/p^s-additive code, from a    */
/*   Zp^s-additive code, a prime p, and a sequence of integers representing  */
/*   the number of coordinates of each type, over Zp, Zp^2,..., Zp^s.        */
/* Input parameters description:                                             */
/*   - code: The linear code over Z/p^s equal to the ZpZp^2..Zp^s-additive   */
/*           code, where the elements in the coordinates over Z/p^i are      */
/*           represented as elements in Z/p^s multiplying by a power of p    */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The new ZpZp^2..Zp^s-additive code                                    */
/*                                                                           */
/*****************************************************************************/
NewCodeMixZp := function(code, p, lengthSeq)
    C := New(MixZpCode);
    C`LengthSeq := lengthSeq;
    C`BaseRing := Integers(p);
    C`Code := code;
    C`Type := Reverse(ZpType(code));
    s := #lengthSeq;

    if (#code eq 1) then
        C`ExtendType := ZeroMatrix(Integers(), s, s);
        C`MinimumHomWeightLowerBound := 0;
        C`MinimumHomWeightUpperBound := 0;
        C`MinimumHomWeight := 0;
        C`MinimumHomWeightWord := code!0;
        C`HomWeightDistribution := [<0,1>];
        return C;
    end if;

    // Trivial lower bound
    C`MinimumHomWeightLowerBound := 1;
    // Trivial upper bount
    //C`MinimumHomWeightUpperBound := MixZpLengthOverZp(C);
    // Singleton upper bound
    singletonBound := MixZpLengthOverZp(C) - Ceiling(Log(p, #code)) +1;
    //singletonBound := MixZpLengthOverZp(C) - &+[i*C`Type[i] : i in [1..s]] +1;
    C`MinimumHomWeightUpperBound := singletonBound;
    if C`MinimumHomWeightLowerBound eq C`MinimumHomWeightUpperBound then
        C`MinimumHomWeight := C`MinimumHomWeightLowerBound;
    end if;

    return C;
end function;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpAdditiveCode                                          */
/* Parameters: M, p, lengthSeq                                               */
/* Function description: Given a matrix over Z/p^s, a prime p, and a sequence*/
/*   of non-negative integers representing the number of coordinates of each */
/*   type, over Zp, Zp^2,..., Zp^s, return the corresponding ZpZp^2..Zp^s-   */
/*   additive code of length lengthSeq generated by the given matrix M.      */
/* Input parameters description:                                             */
/*   - M: A matrix over Z/p^s                                                */
/*   - p: A prime number                                                     */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The ZpZp^2..Zp^s-additive code                                        */
/*                                                                           */
/* Signature: (<ModMatRngElt> M, <RngIntElt> p, <[RngIntElt]> lengthSeq)     */
/*                                                       -> MixZpCode        */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpAdditiveCode(M::ModMatRngElt, p::RngIntElt, lengthSeq::[RngIntElt]
                            : OverMixZp := false) -> MixZpCode
{
Create a ZpZp^2..Zp^s-additive code C in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s given
as a linear code over Zp^s. The parameter OverMixZp specifies whether the elements
in M are elements in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s. The default value is
false and the elements are in Zp^s^(a_1 +...+a_s). If OverMixZp is true, then we
multiply the coordinates in positions X_i=[a_1+...+a_(i-1)+1, ..., a_1+...+a_i]
by p^(s-i) for i in [1,...,s]. The corresponding linear code over Zp^s of C is
obtained by using the function LinearCode() as a subspace of Zp^s^(a_1 +...+a_s)
generated by M, where M is a m x (a_1+..+a_s) matrix over Zp^s.

For i in [1,..,s], the elements of M in coordinate positions X_i can be given as
elements in Z_(p^i) or as elements in p^(s-i)Z_(p^i) subseteq Z_(p^s). If they
are given as elements in Z_(p^i), then they are multiplied by p^(s-i).
}
    require Min(lengthSeq) ge 0: "Argument 3 must be a sequence of non-negative integers";
	require &+lengthSeq eq Ncols(M):
             "Argument 3 is not compatible with the length of the code";
    Zps := Integers(p^#lengthSeq);
    require (Type(BaseRing(M)) eq RngIntRes) and (BaseRing(M) eq Zps):
             "Argument 1 is not a matrix over Z/p^s";
    require IsPrime(p): "Argument 2 must be a prime number";

    if OverMixZp then
		MixZpChangeMatrixZptoZps(~M, p, lengthSeq);
    elif not IsMixZpAdditiveOverZps(M, p, lengthSeq) then
        error "Coordinates must be multiples of powers of p according to argument 3";
    end if;

    return NewCodeMixZp(LinearCode(M), p, lengthSeq);

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpAdditiveCode                                          */
/* Parameters: M, p, lengthSeq                                               */
/* Function description: Given a matrix over Z/p^s, a prime p, and a sequence*/
/*   of non-negative integers representing the number of coordinates of each */
/*   type, over Zp, Zp^2,..., Zp^s, return the corresponding ZpZp^2..Zp^s-   */
/*   additive code of length lengthSeq generated by the given matrix M.      */
/* Input parameters description:                                             */
/*   - M: A matrix over Z/p^s                                                */
/*   - p: A prime number                                                     */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The ZpZp^2..Zp^s-additive code                                        */
/*                                                                           */
/* Signature: (<AlgMatElt> M, <RngIntElt> p, <[RngIntElt]> lengthSeq)        */
/*                                                       -> MixZpCode        */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpAdditiveCode(M::AlgMatElt, p::RngIntElt, lengthSeq::[RngIntElt]
                            : OverMixZp := false) -> MixZpCode
{
Create a ZpZp^2..Zp^s-additive code C in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s given
as a linear code over Zp^s. The parameter OverMixZp specifies whether the elements
in M are elements in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s. The default value is
false and the elements are in Zp^s^(a_1 +...+a_s). If OverMixZp is true, then we
multiply the coordinates in positions X_i=[a_1+...+a_(i-1)+1, ..., a_1+...+a_i]
by p^(s-i) for i in [1,...,s]. The corresponding linear code over Zp^s of C is
obtained by using the function LinearCode() as a subspace of Zp^s^(a_1 +...+a_s)
generated by M, where M is a m x (a_1+..+a_s) matrix over Zp^s.

For i in [1,..,s], the elements of M in coordinate positions X_i can be given as
elements in Z_(p^i) or as elements in p^(s-i)Z_(p^i) subseteq Z_(p^s). If they
are given as elements in Z_(p^i), then they are multiplied by p^(s-i).
}
    require Min(lengthSeq) ge 0: "Argument 3 must be a sequence of non-negative integers";
	require &+lengthSeq eq Ncols(M):
             "Argument 3 is not compatible with the length of the code";
    Zps := Integers(p^#lengthSeq);
    require (Type(BaseRing(M)) eq RngIntRes) and (BaseRing(M) eq Zps):
             "Argument 1 is not a matrix over Z/p^s";
    require IsPrime(p): "Argument 2 must be a prime number";

    if OverMixZp then
		MixZpChangeMatrixZptoZps(~M, p, lengthSeq);
    elif not IsMixZpAdditiveOverZps(M, p, lengthSeq) then
        error "Coordinates must be multiples of powers of p according to argument 3";
    end if;

    return NewCodeMixZp(LinearCode(M), p, lengthSeq);

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpAdditiveCode                                          */
/* Parameters: L, p, lengthSeq                                               */
/* Function description: Given a sequence of vectors over Z/p^s, a prime p,  */
/*   and a sequence of non-negative integers representing the number of      */
/*   coordinates of each type, over Zp, Zp^2,..., Zp^s, return the corres-   */
/*   ponding ZpZp^2..Zp^s-additive code of length lengthSeq generated by the */
/*   given vectors.                                                          */
/* Input parameters description:                                             */
/*   - L: A sequence of vectors over Z/p^s                                   */
/*   - p: A prime number                                                     */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The ZpZp^2..Zp^s-additive code                                        */
/*                                                                           */
/* Signature: (<SeqEnum> L, <RngIntElt> p, <[RngIntElt]> lengthSeq)          */
/*                                                       -> MixZpCode        */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpAdditiveCode(L::[ModTupRngElt], p::RngIntElt, lengthSeq::[RngIntElt]
                            : OverMixZp := false) -> MixZpCode
{
Create a ZpZp^2..Zp^s-additive code C in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s given
as a linear code over Zp^s. The parameter OverMixZp specifies whether the elements
in L are elements in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s. The default value is
false and the elements are in Zp^s^(a_1 +...+a_s). If OverMixZp is true, then we
multiply the coordinates in positions X_i=[a_1+...+a_(i-1)+1, ..., a_1+...+a_i]
by p^(s-i) for i in [1,...,s]. The corresponding linear code over Zp^s of C is
obtained by using the function LinearCode() as a subspace of Zp^s^(a_1 +...+a_s)
generated by L, where L is a sequence of vectors of length a_1+..+a_s over Zp^s.

For i in [1,..,s], the elements of L in coordinate positions X_i can be given as
elements in Z_(p^i) or as elements in p^(s-i)Z_(p^i) subseteq Z_(p^s). If they
are given as elements in Z_(p^i), then they are multiplied by p^(s-i).
}
    require not(IsEmpty(L)): "Argument 1 cannot be empty";
    require Min(lengthSeq) ge 0: "Argument 3 must be a sequence of non-negative integers";
    require &+lengthSeq eq OverDimension(L[1]):
             "Argument 3 is not compatible with the length of the code";
    Zps := Integers(p^#lengthSeq);
    require (Type(BaseRing(L[1])) cmpeq RngIntRes) and (BaseRing(L[1]) cmpeq Zps):
            "Argument 1 does not contain vectors over Z/p^s";
    require IsPrime(p): "Argument 2 must be a prime number";

    M := Matrix(L);
    if OverMixZp then
		MixZpChangeMatrixZptoZps(~M, p, lengthSeq);
    elif not IsMixZpAdditiveOverZps(M, p, lengthSeq) then
        error "Coordinates must be multiples of powers of p according to argument 3";
    end if;

    return NewCodeMixZp(LinearCode(M), p, lengthSeq);

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpAdditiveCode                                          */
/* Parameters: V, p, lengthSeq                                               */
/* Function description: Given a subspace of vectors over Z/p^s, a prime p,  */
/*   and a sequence of non-negative integers representing the number of      */
/*   coordinates of each type, over Zp, Zp^2,..., Zp^s, return the corres-   */
/*   ponding ZpZp^2..Zp^s-additive code of length lengthSeq generated by the */
/*   subspace V.                                                             */
/* Input parameters description:                                             */
/*   - V: A subspace of vectors over Z/p^s                                   */
/*   - p: A prime number                                                     */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The ZpZp^2..Zp^s-additive code                                        */
/*                                                                           */
/* Signature: (<ModTupRng> V, <RngIntElt> p, <[RngIntElt]> lengthSeq)        */
/*                                                       -> MixZpCode        */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpAdditiveCode(V::ModTupRng, p::RngIntElt, lengthSeq::[RngIntElt]
                            : OverMixZp := false) -> MixZpCode
{
Create a ZpZp^2..Zp^s-additive code C in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s given
as a linear code over Zp^s. The parameter OverMixZp specifies whether the elements
in V are elements in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s. The default value is
false and the elements are in Zp^s^(a_1 +...+a_s). If OverMixZp is true, then we
multiply the coordinates in positions X_i=[a_1+...+a_(i-1)+1, ..., a_1+...+a_i]
by p^(s-i) for i in [1,...,s]. The corresponding linear code over Zp^s of C is
obtained by using the function LinearCode() as a subspace of Zp^s^(a_1 +...+a_s)
generated by V, where V is subspace of Zp^s^(a_1+..+a_s).

For i in [1,..,s], the elements of V in coordinate positions X_i can be given as
elements in Z_(p^i) or as elements in p^(s-i)Z_(p^i) subseteq Z_(p^s). If they
are given as elements in Z_(p^i), then they are multiplied by p^(s-i).
}
    require Min(lengthSeq) ge 0: "Argument 3 must be a sequence of non-negative integers";
    require &+lengthSeq eq Degree(V):
             "Argument 3 is not compatible with the length of the code";
    Zps := Integers(p^#lengthSeq);
    require (Type(BaseRing(V)) cmpeq RngIntRes) and (BaseRing(V) cmpeq Zps):
            "Argument 1 does not contain vectors over Z/p^s";
    require IsPrime(p): "Argument 2 must be a prime number";

    M := Matrix(Basis(V));
    if OverMixZp then
		MixZpChangeMatrixZptoZps(~M, p, lengthSeq);
    elif not IsMixZpAdditiveOverZps(M, p, lengthSeq) then
        error "Coordinates must be multiples of powers of p according to argument 3";
    end if;

    return NewCodeMixZp(LinearCode(M), p, lengthSeq);

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpAdditiveCode                                          */
/* Parameters: C, p, lengthSeq                                               */
/* Function description: Given a linear code over Z/p^s, a prime p, and a    */
/*   sequence of non-negative integers representing the number of            */
/*   coordinates of each type, over Zp, Zp^2,..., Zp^s, return the corres-   */
/*   ponding ZpZp^2..Zp^s-additive code of length lengthSeq generated by the */
/*   codewords in C.                                                         */
/* Input parameters description:                                             */
/*   - C: A linear over Z/p^s                                                */
/*   - p: A prime number                                                     */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The ZpZp^2..Zp^s-additive code                                        */
/*                                                                           */
/* Signature: (<CodeLinRng> C, <RngIntElt> p, <[RngIntElt]> lengthSeq)       */
/*                                                       -> MixZpCode        */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpAdditiveCode(C::CodeLinRng, p::RngIntElt, lengthSeq::[RngIntElt]
                            : OverMixZp := false) -> MixZpCode
{
Create a ZpZp^2..Zp^s-additive code C in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s given
as a linear code over Zp^s. The parameter OverMixZp specifies whether the elements
in C are elements in Zp^a_1 x Zp^2^a_2 x ... x Zp^s^a_s. The default value is
false and the elements are in Zp^s^(a_1 +...+a_s). If OverMixZp is true, then we
multiply the coordinates in positions X_i=[a_1+...+a_(i-1)+1, ..., a_1+...+a_i]
by p^(s-i) for i in [1,...,s]. The corresponding linear code over Zp^s of C is
obtained by using the function LinearCode() as a subspace of Zp^s^(a_1 +...+a_s)
generated by V, where V is subspace of Zp^s^(a_1+..+a_s).

For i in [1,..,s], the elements of C in coordinate positions X_i can be given as
elements in Z_(p^i) or as elements in p^(s-i)Z_(p^i) subseteq Z_(p^s). If they
are given as elements in Z_(p^i), then they are multiplied by p^(s-i).
}
    require Min(lengthSeq) ge 0: "Argument 3 must be a sequence of non-negative integers";
    require &+lengthSeq eq Length(C):
             "Argument 3 is not compatible with the length of the code";
    Zps := Integers(p^#lengthSeq);
    require (Type(BaseRing(C)) cmpeq RngIntRes) and (BaseRing(C) cmpeq Zps):
            "Argument 1 does not contain vectors over Z/p^s";
    require IsPrime(p): "Argument 2 must be a prime number";

    if (#C eq 1) then
        return MixZpAdditiveZeroCode(p, lengthSeq);
    end if;

    M := Matrix(Basis(VectorSpace(C)));
    if OverMixZp then
		MixZpChangeMatrixZptoZps(~M, p, lengthSeq);
    elif not IsMixZpAdditiveOverZps(M, p, lengthSeq) then
        error "Coordinates must be multiples of powers of p according to argument 3";
    end if;

    D := NewCodeMixZp(LinearCode(M), p, lengthSeq);

    //assign the minimum homogeneus weight or update the lower and upper bounds
    //if over_Z4(C) and assigned(C`MinimumLeeWeight) then
    //    UpdateMinimumHomWeightLowerBound(~D, C`MinimumLeeWeight - alpha);
    //    UpdateMinimumHomWeightUpperBound(~D, C`MinimumLeeWeight);
    //else
    //    UpdateMinimumHomWeightLowerBound(~D, C`MinimumWeightLowerBound);
    //    UpdateMinimumHomWeightUpperBound(~D, 2*C`MinimumWeightUpperBound);
    //end if;

    return D;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpAdditiveCode                                          */
/* Parameters: C, s                                                          */
/* Function description: Given a linear code C over Z/p^i, 1 ≤ i ≤ s, of type*/
/*   (n;t_1,..., t_i), return the ZpZp^2..Zp^s-additive code of type (a_1,   */
/*   ...,a_s; t_1,...,t_i,0,...,0) corresponding to C, where a_i=n and a_j=0 */
/*   for all j in {1,...,s}\{i}.                                             */
/* Input parameters description:                                             */
/*   - C: A linear over Z/p^s                                                */
/*   - s: An integer number s >= i                                           */
/* Output parameters description:                                            */
/*   - The ZpZp^2..Zp^s-additive code                                        */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<CodeLinRng> C, <RngIntElt> s) -> MixZpCode                   */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpAdditiveCode(C::CodeLinRng, s::RngIntElt) -> MixZpCode
{
Given a linear code C over Z/p^i, 1 ≤ i ≤ s, of type (n; t_1,..., t_i), return
the ZpZp^2..Zp^s-additive code of type (a_1,...,a_s; t_1,...,t_i,0,...,0)
corresponding to C, where a_i=n and a_j=0 for all j in [1,..., s]\[i].
}
    isOverZps, p, i := IsLinearCodeOverZps(C);
    require isOverZps and (i ge 1): "The code must be over Z/p^i, with i>=1";
    require i le s: "Argument 2 must be greater than or equal to", i;

    G := ChangeRing(GeneratorMatrix(C), Integers(p^s));
    lengthSeq := [0^^s];
    lengthSeq[i] := NumberOfColumns(G);

    return MixZpAdditiveCode(G, p, lengthSeq : OverMixZp := true);

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpAdditiveCode                                          */
/* Parameters: T                                                             */
/* Function description: Given a sequence T of elements of the cartesian     */
/*   product set Zp^(a_1) × Zp2^(a_2) ×...× (Zp^s)^a_s, return the ZpZp^2... */
/*   additive code of type (a_1,..., a_s; t_1,..., t_s) generated by T. The  */
/*   code is represented as a linear code over Z_p^s after multiplying the   */
/*   coordinates in positions X_i = {a_1 +...+ a_{i−1} + 1,..., a_1 +...+    */
/*   a_i} by p^{s−i} for i in {1,..., s}.                                    */
/* Input parameters description:                                             */
/*   - T: A sequence of elements of the cartesian product set Zp^(a_1) ×     */
/*        Zp2^(a_2) ×...× (Zp^s)^a_s                                         */
/* Output parameters description:                                            */
/*   - The ZpZp^2..Zp^s-additive code                                        */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: ([<Tup>] T) -> MixZpCode                                       */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpAdditiveCode(T::[Tup]) -> MixZpCode
{
Given a sequence T of elements of the cartesian product set Zp^(a_1) × Zp2^(a_2)
×...× (Zp^s)^a_s, return the ZpZp^2..Zp^s-additive code of type (a_1,..., a_s;
t_1,..., t_s) generated by T. The code is represented as a linear code over Z_p^s
after multiplying the coordinates in positions X_i = [a_1 +...+ a_(i−1) + 1,...,
a_1 +...+ a_i] by p^(s−i) for i in [1,..., s].
}
    require not IsEmpty(T): "Argument cannot be empty";

    s := #T[1];
    for i in [1..s] do
        require Type(T[1][i]) cmpeq ModTupRngElt:
            "Argument must be a sequence of tuples containing vectors over a ring";
    end for;
    R := BaseRing(T[1][1]);
    isFiniteRing, p := IsFinite(R);
    require isFiniteRing: "The vectors in the tuples must be over a finite ring";
    for i in [1..s] do
        require BaseRing(T[1][i]) eq Integers(p^i):
            "The i-th component vector in the tuples must be over the ring Z/p^i";
    end for;
    require IsPrime(p): "The first vector in the tuples must be over Z/p, with p prime";

    // Convert each tuple to a vector over Z/p^s
    //L := [FromMixZptoZps(T[i], p) : i in [1..#T]];
    L := FromMixZptoZps(T, p);
    lengthSeq := [Ncols(T[1][i]) : i in [1..s]];

    return MixZpAdditiveCode(L, p, lengthSeq);

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////            SOME TRIVIAL ZpZp^2..Zp^s-ADDITIVE CODES             ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpAdditiveUniverseCode                                  */
/* Parameters: p, lengthSeq                                                  */
/* Function description: Given a prime number p and a sequence of non-       */
/*   negative integers lengthSeq, return the ZpZp^2..Zp^s-additive code of   */
/*   type (lengthSeq; lengthSeq) consisting of all possible codewords.       */
/* Input parameters description:                                             */
/*   - p: A prime number                                                     */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The ZpZp^2..Zp^s-additive universe code                               */
/*                                                                           */
/* Signature: (<RngIntElt> p, <[RngIntElt]> lengthSeq) -> MixZpCode          */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpAdditiveUniverseCode(p::RngIntElt, lengthSeq::[RngIntElt]) -> MixZpCode
{
Given a prime number p and a sequence of non-negative integers lengthSeq, return the
ZpZp^2..Zp^s-additive code of type (lengthSeq; lengthSeq) consisting of all
possible codewords.
}
    require Min(lengthSeq) ge 0: "Argument 2 must be a sequence of non-negative integers";
    require &+lengthSeq gt 0:
        "Argument 2 must be a sequence such that the sum of its elements is greater than 0";
    require IsPrime(p): "Argument 1 must be a prime number";

    s := #lengthSeq;
    Zps := Integers(p^s);
    G := DiagonalMatrix(Zps, &cat[[(p^(s-i))^^lengthSeq[i]] :  i in [1..s]]);
    C := MixZpAdditiveCode(G, p, lengthSeq);

    C`ExtendType := DiagonalMatrix(Integers(), lengthSeq);

    // compute the position of the first non-zero element in lengthSeq
    minNotZeroType := 1;
    while IsZero(lengthSeq[minNotZeroType]) do
        minNotZeroType +:=1;
    end while;
    // compute the minimum homogeneous weight
    if (minNotZeroType eq 1) then
        minHomWeight := 1;
    else
        minHomWeight := p^(minNotZeroType-2)*(p-1);
    end if;
    C`MinimumHomWeightLowerBound := minHomWeight;
    C`MinimumHomWeightUpperBound := minHomWeight;
    C`MinimumHomWeight := minHomWeight;
    C`MinimumHomWeightWord := G[1];
    //C`HomWeightDistribution := [<0,1> ...];

    return C;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpAdditiveZeroCode                                      */
/* Parameters: p, lengthSeq                                                  */
/* Function description: Given a prime number p and a sequence of non-       */
/*   negative integers lengthSeq, return the ZpZp^2..Zp^s-additive code of   */
/*   type (lengthSeq; 0,...,0) consisting of only the zero codeword.         */
/* Input parameters description:                                             */
/*   - p: A prime number                                                     */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - The ZpZp^2..Zp^s-additive zero code                                   */
/*                                                                           */
/* Signature: (<RngIntElt> p, <[RngIntElt]> lengthSeq) -> MixZpCode          */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpAdditiveZeroCode(p::RngIntElt, lengthSeq::[RngIntElt]) -> MixZpCode
{
Given a prime number p and a sequence of non-negative integers lengthSeq, return the
ZpZp^2..Zp^s-additive code of type (lengthSeq; 0,...,0) consisting of only the zero
codeword.
}
    require Min(lengthSeq) ge 0: "Argument 2 must be a sequence of non-negative integers";
    require &+lengthSeq gt 0:
        "Argument 2 must be a sequence such that the sum of its elements is greater than 0";
    require IsPrime(p): "Argument 1 must be a prime number";

    s := #lengthSeq;
    Zps := Integers(p^s);

    return MixZpAdditiveCode(Matrix(Zps, [[0 : i in [1..&+lengthSeq]]]), p, lengthSeq);
    //the minimum weight and bounds are assigned in NewCodeMixZp function

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////            RANDOM ZpZp^2..Zp^s-ADDITIVE CODES                   ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: RandomMixZpAdditiveCode                                    */
/* Parameters: p, lengthSeq                                                  */
/* Function description: Given a prime number p and a sequences of non-      */
/*   negative integers lengthSeq, return a random ZpZp^2..Zp^s-additive code */
/*   of type (lengthSeq; t_1,..,t_s) for some non-negative integers t_1,..,  */
/*   t_s.                                                                    */
/* Input parameters description:                                             */
/*   - p: A prime number                                                     */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - A random ZpZp^2..Zp^s-additive code                                   */
/*                                                                           */
/* Signature: (<RngIntElt> p, <[RngIntElt]> lengthSeq) -> MixZpCode          */
/*                                                                           */
/*****************************************************************************/
intrinsic RandomMixZpAdditiveCode(p::RngIntElt, lengthSeq::[RngIntElt]) -> MixZpCode
{
Given a prime number p and a sequences of non-negative integers lengthSeq, return
a random ZpZp^2..Zp^s-additive code of type (lengthSeq; t_1,..,t_s) for some
non-negative integers t_1,..., t_s.
}
    require Min(lengthSeq) ge 0: "Argument 2 must be a sequence of non-negative integers";
    n := &+lengthSeq;
    require n gt 0:
        "Argument 2 must be a sequence such that the sum of its elements is greater than 0";
    require IsPrime(p): "Argument 1 must be a prime number";

    k := Random(n);
    _, G := RandomZpAdditiveCode(p, n, #lengthSeq, k);

    MixZpChangeMatrixZptoZps(~G, p, lengthSeq);
    return MixZpAdditiveCode(G, p, lengthSeq);

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////            BASIC NUMERICAL INVARIANTS                           ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpLength                                                */
/* Parameters: C                                                             */
/* Function description: Given a ZpZp^2..Zp^s-additive code C of type        */
/*   (lengthSeq; typeSeq), return the length n = &+lengthSeq, and the        */
/*   sequence lengthSeq with lengthSeq[i] the number of coordinates over     */
/*   Z/2^i for i in [1..s].                                                  */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - The length of the ZpZp^2..Zp^s-additive code C                        */
/*   - The sequence lengthSeq of non-negative integers                       */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> RngIntElt, SeqEnum                          */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpLength(C::MixZpCode) -> RngIntElt, SeqEnum
{
Given a ZpZp^2..Zp^s-additive code C of type (lengthSeq; typeSeq), return the
length n = &+lengthSeq, and the sequence lengthSeq with lengthSeq[i] the number
of coordinates over Z/2^i for i in [1..s].
}
    return Length(C`Code), C`LengthSeq;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpLengthOverZp                                          */
/* Parameters: C                                                             */
/* Function description: Given a ZpZp^2..Zp^s-additive code C of type        */
/*   (lengthSeq; typeSeq), return the length n_p = a_1 + p*a_2 + ..+ p^(s-1)**/
/*   a_s, where lengthSeq=[a_1,..,a_s], which corresponds to the length of   */
/*   the code C_p = Phi(C) over Zp, where Phi is the Gray map considered in  */
/*   this package.                                                           */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - The length of the code Cp = Phi(C) over Zp                            */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> RngIntElt                                   */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpLengthOverZp(C::MixZpCode) -> RngIntElt
{
Given a ZpZp^2..Zp^s-additive code C of type (lengthSeq; typeSeq), return the
length n_p = a_1 + p*a_2 + ..+ p^(s-1)*a_s, where lengthSeq=[a_1,..,a_s], which
corresponds to the length of the code C_p = Phi(C) over Zp, where Phi is the
Gray map considered in this package.
}
    p := #C`BaseRing;
    return &+[ C`LengthSeq[i] * p^(i-1) : i in [1..#C`LengthSeq] ];

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpType                                                  */
/* Parameters: C                                                             */
/* Function description: Given a ZpZp^2..Zp^s-additive code C of type        */
/*   (lengthSeq; typeSeq), return both sequences lengthSeq and typeSeq.      */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - The sequence lengthSeq of non-negative integers                       */
/*   - The sequence typeSeq of non-negative integers                         */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> SeqEnum, SeqEnum                            */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpType(C::MixZpCode) -> SeqEnum
{
Given a ZpZp^2..Zp^s-additive code C of type (lengthSeq; typeSeq), return both
sequences lengthSeq and typeSeq.
}
    return C`LengthSeq, Reverse(ZpType(C`Code));

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: #                                                          */
/* Parameters: C                                                             */
/* Function description: Given a ZpZp^2..Zp^s-additive code C of type        */
/*   (lengthSeq; typeSeq), return the number of codewords belonging to C,    */
/*   that is, p^(t_1+2t_2+..+st_s), where typeSeq = [t_1,t_2,..,t_s].        */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - The number of codewords of C                                          */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> RngIntElt                                   */
/*                                                                           */
/*****************************************************************************/
intrinsic '#'(C::MixZpCode) -> RngIntElt
{
Given a ZpZp^2..Zp^s-additive code C of type (lengthSeq; typeSeq), return the
number of codewords belonging to C, that is, p^(t_1+2t_2+..+st_s), where
typeSeq = [t_1,t_2,..,t_s].
}
    return #C`Code;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: InformationRate                                            */
/* Parameters: C                                                             */
/* Function description: Given a ZpZp^2..Zp^s-additive code C of type        */
/*   (lengthSeq; typeSeq), return the information rate of C, that is, the    */
/*   ratio (t_1+2t_2+..+st_s)/n_p, where typeSeq = [t_1,..,t_s], lengthSeq = */
/*   [a_1,..,a_s], and n_p = a_1 + p*a_2 +..+ p^(s-1)*a_s.                   */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - The information rate of C                                             */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> FldRatElt                                   */
/*                                                                           */
/*****************************************************************************/
intrinsic InformationRate(C::MixZpCode) -> FldRatElt
{
Given a ZpZp^2..Zp^s-additive code C of type (lengthSeq; typeSeq), return the
information rate of C, that is, the ratio (t_1+2t_2+..+st_s)/n_p, where typeSeq =
[t_1,..,t_s], lengthSeq = [a_1,..,a_s], and n_p = a_1 + p*a_2 +..+ p^(s-1)*a_s.
}
    p := #C`BaseRing;
    return Log(p, #C) / MixZpLengthOverZp(C);

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////                   THE GRAY MAP FUNCTIONS                       ////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: CarletGrayMap                                              */
/* Parameters:  C                                                            */
/* Function description: Given a ZpZp^2..Zp^s-additive code, return the Gray */
/*   map Phi for C. This is the map from C to Phi(C).                        */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - A map from C to Phi(C)                                                */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> Map                                         */
/*                                                                           */
/*****************************************************************************/
intrinsic CarletGrayMap(C::MixZpCode) -> Map
{
Given a ZpZp^2..Zp^s-additive code, return the generalized Gray map Phi for C.
This is the map from C to Phi(C).
}
    //Codomain
    p := #C`BaseRing;
    Vn := VectorSpace(GF(p), MixZpLengthOverZp(C));

    //Sequence with the different Gray maps
    s := #C`LengthSeq;
    mapsSeq := [ CarletGrayMap(p, i) : i in [1..s] ];

    Lseq := MixZpCoordinatesPartition(C`LengthSeq);
    return map< C`Code -> Vn | c :-> Vn!Flat( [[GF(p)!(c[j] div p^(s-1)) : j in Lseq[1] ]] cat
                                [Flat( [ Eltseq( mapsSeq[i](Integers(p^i)!(c[j] div p^(s-i))))
                                                          : j in Lseq[i] ]) : i in [2..s] ])>;
                          //y :-> [ Flat([ (c[j], i) : j in Lseq[i]])  : i in [1..s]]  >;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: CarletGrayMapImage                                         */
/* Parameters:  C                                                            */
/* Function description: Given a ZpZp^2..Zp^s-additive code of type          */
/*   (lengthSeq, typeSeq), return the image of C under the generalized Gray  */
/*   map Phi as a sequence of vectors in GF(p)^n_p, where n_p = a_1+p*a_2+   */
/*   ..+ p^(s-1)a_s and lengthSeq = [a_1,..,a_s]. As the resulting image may */
/*   not be a linear code over GF(p), a sequence of vectors is returned      */
/*   rather than a code.                                                     */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - A sequence of vectors over GF(p)                                      */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> [ModTupFldElt]                              */
/*                                                                           */
/*****************************************************************************/
intrinsic CarletGrayMapImage(C::MixZpCode) -> SeqEnum //[ModTupFldElt]
{
Given a ZpZp^2..Zp^s-additive code of type (lengthSeq, typeSeq), return the image
of C under the generalized Gray map Phi as a sequence of vectors in Fp^n_p, where
n_p = a_1 + p*a_2 + ..+ p^(s-1)a_s and lengthSeq = [a_1,..,a_s]. As the resulting
image may not be a linear code over Fp, a sequence of vectors is returned rather
than a code.
}
    mapGray := CarletGrayMap(C);

    return [mapGray(c) : c in C`Code];

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: HasLinearCarletGrayMapImage                                */
/* Parameters:  C                                                            */
/* Function description: Given a ZpZp^2..Zp^s-additive code, return true if  */
/*   and only if the image of C under the generalized Gray map Phi is a      */
/*   linear code over GF(p). If so, the function also returns the image B as */
/*   a linear code, together with the bijection Phi : C -> B.                */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - true if and only if the image of C under Phi is a linear code         */
/*   - The linear code over GF(p) if return true                             */
/*   - The bijection Phi: C -> B if return true                              */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> BoolElt, CodeLinFld, Map                    */
/*                                                                           */
/*****************************************************************************/
intrinsic HasLinearCarletGrayMapImage(C::MixZpCode) -> BoolElt, CodeLinFld, Map
{
Given a ZpZp^2..Zp^s-additive code, return true if and only if the image of C
under the generalized Gray map Phi is a linear code over GF(p). If so, the
function also returns the image B as a linear code, together with the bijection
Phi : C -> B.
}
    isLinear := HasLinearCarletGrayMapImage(C`Code);
    if isLinear then
        Cp := LinearCode(Matrix(CarletGrayMapImage(C)));
        mapGray := CarletGrayMap(C);
        bijection := map<C -> Cp  | v :-> mapGray(v)>;
        //w :-> w @@ mapGray >;
        return true, Cp, bijection;
    else
        return false;
    end if;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////             CONSTRUCTION OF ZpZp^2..Zp^s-HADAMARD CODES        ////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: MatrixPartition                                            */
/* Parameters: M, lengthSeq                                                  */
/* Function description: Given a matrix M and a sequence of non-negative     */
/*   integers [a_1,...,a_s], return a tuple with s submatrices of M, such    */
/*   that the submatrix in the i-th position is the one having the columns   */
/*   in Xi = {a_1+...+a_(i-1)+1, .., a_1+...+a_i}                            */
/* Input parameters description:                                             */
/*   - M: A matrix over Z/p^s                                                */
/*   - lengthSeq: A sequence of non-negative integers of size s              */
/* Output parameters description:                                            */
/*   - A tuple with column submatrices of M                                  */
/*                                                                           */
/*****************************************************************************/
function MatrixPartition(M, lengthSeq)
    i := 1;
    Mtup := <>;
    for alpha in lengthSeq do
        Append(~Mtup, ColumnSubmatrix(M, i, alpha));
        i +:= alpha;
    end for;
    return Mtup;
end function;

/*****************************************************************************/
/*                                                                           */
/* Function name: MatrixRepetition                                           */
/* Parameters: M, newRow                                                     */
/* Function description: Given a matrix M over Zp^s and a sequence newRow of */
/*   k integers, return a matrix [M_1,...,M_k] over Zp^s, where M_i is       */
/*   obtained by appending to M a final row consisting of the i-th entry in  */
/*   newRow repeated n times, where n is the number of columns of M.         */
/* Input parameters description:                                             */
/*   - M: A matrix over Z/p^s                                                */
/*   - newRow: A sequence of k integers                                      */
/* Output parameters description:                                            */
/*   - A matrix over Z/p^s                                                   */
/*                                                                           */
/*****************************************************************************/
function MatrixRepetition(M, newRow)
    rowMatrix := HorizontalJoin(<M : i in [1..#newRow]>);
    rowVector := Matrix(BaseRing(M), [&cat[[a^^Ncols(M)] : a in newRow]]);
    return VerticalJoin(rowMatrix, rowVector);
end function;

/*****************************************************************************/
/*                                                                           */
/* Function name: ExtraColumnMatrix                                          */
/* Parameters: s, p, i, rep                                                  */
/* Function description: Given integers s, i and rep, and a prime p return a */
/*   matrix over Zp^s whose columns are all the possible y=[p^i,y',1]^T,     */
/*   where y' is an element of the cartesian product (p*Zp^i)^rep.           */
/* Input parameters description:                                             */
/*   - s: An integer number                                                  */
/*   - p: A prime number                                                     */
/*   - i: An integer number                                                  */
/*   - rep: An integer number                                                */
/* Output parameters description:                                            */
/*   - A matrix over Z/p^s                                                   */
/*                                                                           */
/*****************************************************************************/
ExtraColumnMatrix := function(s, p, i, rep)
    P := [ {p^i} ] cat [ {(p*y) : y in [0..p^i-1]}^^rep ];
    carP := Set(CartesianProduct(P));
    matP := [[a : a in v] : v in carP ];

    Mt := Transpose(Matrix(Integers(p^s), matP));
    return MatrixRepetition(Mt, [1..p-1] );
end function;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpHadamardRecConst                                      */
/* Parameters: M, p, lengthSeq, Iinc                                         */
/* Function description: Given a matrix M, a prime p, a sequence of integers */
/*   lengthSeq, and an integer Iing, perform a step in the recursive         */
/*   construction of a generator matrix for a ZpZp^2..Zp^s-additive GH code, */
/*   as described in (*). Matrix M corresponds to a generator matrix of a    */
/*   ZpZp^2...Zp^s-additive GH code of type (lengthSeq; t1,t2,...,ts), and   */
/*   this function returns a generator matrix for a ZpZp^2...Zp^s-additive   */
/*   GH code of type (lengthSeq; t1',t2',...,ts'), with t_{Iinc}'=t_{Iinc}+1 */
/*   and t_j'=t_j for any j different than Iinc.                             */
/* Input parameters description:                                             */
/*   - M: A matrix over Zp^s, which is a generator matrix of a ZpZp^2...Zp^s-*/
/*        additive GH code of type (lengthSeq; t1,...,ts)                    */
/*   - p: A prime number                                                     */
/*   - lengthSeq: A sequence of integers                                     */
/*   - Iinc: An integer number                                               */
/* Output parameters description:                                            */
/*   - A matrix over Zp^s, which is a generator matrix of a ZpZp^2...Zp^s-   */
/*     additive GH code of type (lengthSeq; t1,..,t_Iinc+1,..,ts)            */
/*                                                                           */
/*****************************************************************************/
MixZpHadamardRecConst := function(M, p, lengthSeq, Iinc)
    Hseq := MatrixPartition(M, lengthSeq);
    s := #lengthSeq;
    Zs := Integers(p^s);

    M1 := MatrixRepetition(Hseq[1], [0..p-1] );
    newHseq := <M1>;
    if Iinc eq s then
       for i in [2..s] do
           Mi :=  MatrixRepetition(Hseq[i], [(p^(i-1))*j : j in [0..p-1]] );
           Append(~newHseq, Mi);
       end for;
    end if;

    if Iinc in [1..s-1] then
        for j in [1..s-Iinc] do
            M2a := ExtraColumnMatrix(s, p, j, Nrows(Hseq[1])-1);
            M2b :=  MatrixRepetition(Hseq[j+1], [u : u in [0..p^(j+1)-1]] );
            M2 := HorizontalJoin(M2a, M2b);

            Append(~newHseq, M2);
        end for;
        for j in [s-Iinc+1..s-1] do
            M3 :=  MatrixRepetition(Hseq[j+1], [p^(j-s+Iinc)*u : u in [0..p^(s-Iinc+1)-1]] );
            Append(~newHseq, M3);
        end for;
    end if;

    newLengthSeq := [Ncols(M) : M in newHseq];
    newM := HorizontalJoin(newHseq);
    C := MixZpAdditiveCode(newM, p, newLengthSeq : OverMixZp := true);

    return C, newM, newLengthSeq;
end function;

/*****************************************************************************/
/*                                                                           */
/* Function name: MixZpHadamardCode                                          */
/* Parameters: p, L                                                          */
/* Function description: Given a prime number p and a sequence L of non-     */
/*   negative integers, return a ZpZp^2..Zp^s-additive Hadamard code of type */
/*   (a_1,..,a_s; L) along with a generator matrix. The parameter OverZps    */
/*   specifies whether the code is over Z_p^s, that is with a_1=..=a_(s-1)=0,*/
/*   or, otherwise, a_1<>0, ..., a_(s-1)<>0. The default value is false.     */
/* Input parameters description:                                             */
/*   - p: A prime number                                                     */
/*   - L: A sequence of non-negative integers                                */
/* Output parameters description:                                            */
/*   - A ZpZp^2..Zp^s-additive Hadamard code of type L=[t1,..,ts]            */
/*   - A generator matrix of the ZpZp^2..Zp^s-additive Hadamard code         */
/*                                                                           */
/* Function developed by Dipak K. Bhunia                                     */
/*                                                                           */
/* Signature: (<IntRngElt> p, <SeqEnum> L) -> MixZpCode, ModMatRngElt        */
/*                                                                           */
/*****************************************************************************/
intrinsic MixZpHadamardCode(p::RngIntElt, L:: SeqEnum : OverMixZp := true)
                                                      -> MixZpCode, ModMatRngElt
{
Given a prime number p and a sequence L of non-negative integers, return a
ZpZp^2..Zp^s-additive Hadamard code of type (a_1,..,a_s; L) along with a generator
matrix. The parameter OverZps specifies whether the code is over Z_p^s, that is
with a_1=...=a_(s-1)=0, or, otherwise, a_1<>0, ..., a_(s-1)<>0. The default value
is false.
}
    require IsPrime(p): "The first parameter must be a prime number";
    s := #L;
    require L[s] ge 1: "The last integer in argument 2 must be greater than 0";
    if OverMixZp then
        require L[1] ge 1: "The first integer in argument 2 must be greater than 0";
    end if;

    if not OverMixZp then
        CZps := ZpHadamardCode(p, Reverse(L));
        return MixZpAdditiveCode(CZps, p, [0^^(s-1)] cat [Length(CZps)]);
    end if;

    // The implementation take into account that the type is Reverse(L)!
    L := Reverse(L);

    s := #L;
    Zs := Integers(p^s);

    // Construct the first ZpZp^2..Zp^s-additive Hadamard code of type (1,0,1)
    row1 := [1^^p] cat &cat[ [(p^(i-1))^^(p-1)]  : i in [2..s]];
    row2:= [0..(p-1)] cat &cat[ [1..p-1] : i in [2..s] ];
    M := Matrix(Zs, [row1, row2]);
    lengthSeq := [p] cat [(p-1)^^(s-1)];
    C := MixZpAdditiveCode(M, p, lengthSeq : OverMixZp := true);

    // Construct the ZpZp^2..Zp^s-additive Hadamard code of type L recursively
    T := L;
    T[1] := L[1] - 1;
    T[s] := L[s] - 1;
    for i in [1..s] do
        for j in [1..T[i]] do
            C, M, lengthSeq := MixZpHadamardRecConst(M, p, lengthSeq, i);
        end for;
    end for;

    return C, M;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////                        THE CODE SPACE                           ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: Name                                                       */
/* Parameters: C, i                                                          */
/* Function description: Given a ZpZp^2..Zp^s-additive code C of type        */
/*   (a_1,...,a_s; t_1,...,t_s) and a positive integer j, return the j-th    */
/*   generator of C as a linear code over Zp^s, where the coordinates in     */
/*   positions Xi = {a_1+...+a_(i-1)+1, ..,a_1+...+a_i} are multiplied by    */
/*   p^(s-1) for i in {1,...,s}.                                             */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/*   - i: A positive integer                                                 */
/* Output parameters description:                                            */
/*   - The i-th generator of C                                               */
/*                                                                           */
/* Signature: (<MixZpCode> C, <RngIntElt> i) -> ModTupRngElt                 */
/*                                                                           */
/*****************************************************************************/
intrinsic Name(C::MixZpCode, i::RngIntElt) -> ModTupRngElt
{
Given a ZpZp^2..Zp^s-additive code C of type (a_1,...,a_s; t_1,...,t_s) and a
positive integer j, return the j-thgenerator of C as a linear code over Zp^s,
where the coordinates in positions Xi = [a_1+...+a_(i-1)+1,...,a_1+...+a_i] are
multiplied by p^(s-1) for i in [1,...,s].
}
    requirerange i, 1, Ngens(C`Code);

    return C`Code.i;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: .                                                          */
/* Parameters: C, i                                                          */
/* Function description: Given a ZpZp^2..Zp^s-additive code C of type        */
/*   (a_1,...,a_s; t_1,...,t_s) and a positive integer j, return the j-th    */
/*   generator of C as a linear code over Zp^s, where the coordinates in     */
/*   positions Xi = {a_1+...+a_(i-1)+1,...,a_1+...+a_i} are multiplied by    */
/*   p^(s-1) for i in {1,...,s}.                                             */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/*   - i: A positive integer                                                 */
/* Output parameters description:                                            */
/*   - The i-th generator of C                                               */
/*                                                                           */
/* Signature: (<MixZpCode> C, <RngIntElt> i) -> ModTupRngElt                 */
/*                                                                           */
/*****************************************************************************/
intrinsic '.'(C::MixZpCode, i::RngIntElt) -> ModTupRngElt
{
Given a ZpZp^2..Zp^s-additive code C of type (a_1,...,a_s; t_1,...,t_s) and a
positive integer j, return the j-thgenerator of C as a linear code over Zp^s,
where the coordinates in positions Xi = [a_1+...+a_(i-1)+1,...,a_1+...+a_i] are
multiplied by p^(s-1) for i in [1,...,s].
}
    requirerange i, 1, Ngens(C`Code);

    return C`Code.i;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: Set                                                        */
/* Parameters: C                                                             */
/* Function description: Given a ZpZp^2..Zp^s-additive code C of type        */
/*   (a_1,...,a_s; t_1,...,t_s), return the set containing all its codewords,*/
/*   where the coordinates in positions Xi = {a_1+...+a_(i-1)+1,...,a_1+...  */
/*   +a_s} are multiplied by p^(s-1) for i in {1,...,s}.                     */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2...Zp^s-additive code                                      */
/* Output parameters description:                                            */
/*   - The set with all codewords of the code C                              */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> SetEnum                                     */
/*                                                                           */
/*****************************************************************************/
intrinsic Set(C::MixZpCode) -> SetEnum
{
Given a ZpZp^2...Zp^s-additive code C of type (a_1,...,a_s; t_1,...,t_s), return
the set containing all its codewords, where the coordinates in positions
Xi = [a_1+...+a_(i-1)+1,...,a_1+...+a_s] are multiplied by p^(s-1) for i in [1,...,s].
}
    return Set(C`Code);

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////                  MEMBERSHIP AND EQUALITY                        ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: eq                                                         */
/* Parameters: C, D                                                          */
/* Function description: Return true if and only if the ZpZp^2..Zp^s-additive*/
/*   codes C and D are equal.                                                */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/*   - D: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - True if C is equal to D, and false otherwise                          */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<MixZpCode> C, <MixZpCode> D) -> BoolElt                      */
/*                                                                           */
/*****************************************************************************/
intrinsic 'eq'(C::MixZpCode, D::MixZpCode) -> BoolElt
{
Return true if and only if the ZpZp^2..Zp^s-additive codes C and D are equal.
}
    if C`LengthSeq eq D`LengthSeq then
        return C`Code eq D`Code;
    else
        return false;
    end if;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: ne                                                         */
/* Parameters: C, D                                                          */
/* Function description: Return true if and only if the ZpZp^2..Zp^s-additive*/
/*   codes C and D are not equal.                                            */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/*   - D: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - True if C is not equal to D, and false otherwise                      */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<MixZpCode> C, <MixZpCode> D) -> BoolElt                      */
/*                                                                           */
/*****************************************************************************/
intrinsic 'ne'(C::MixZpCode, D::MixZpCode) -> BoolElt
{
Return true if and only if the ZpZp^2..Zp^s-additive codes C and D are not equal.
}
    return not(C eq D);

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: subset                                                     */
/* Parameters: C, D                                                          */
/* Function description: Return true if and only if the ZpZp^2..Zp^s-additive*/
/*   code C is a subcode of the ZpZp^2..Zp^s-additive code D.                */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/*   - D: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - True if C is a subcode of D, and false otherwise                      */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<MixZpCode> C, <MixZpCode> D) -> BoolElt                      */
/*                                                                           */
/*****************************************************************************/
intrinsic 'subset'(C::MixZpCode, D::MixZpCode) -> BoolElt
{
Return true if and only if the ZpZp^2..Zp^s-additive code C is a subcode of the
ZpZp^2..Zp^s-additive code D.
}
    if (C`LengthSeq eq D`LengthSeq) then
        return C`Code subset D`Code;
    else
        return false;
    end if;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: notsubset                                                  */
/* Parameters: C, D                                                          */
/* Function description: Return true if and only if the ZpZp^2..Zp^s-additive*/
/*   code C is not a subcode of the ZpZp^2..Zp^s-additive code D.            */
/* Input parameters description:                                             */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/*   - D: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - True if C is not a subcode of D, and false otherwise                  */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<MixZpCode> C, <MixZpCode> D) -> BoolElt                      */
/*                                                                           */
/*****************************************************************************/
intrinsic 'notsubset'(C::MixZpCode, D::MixZpCode) -> BoolElt
{
Return true if and only if the ZpZp^2..Zp^s-additive code C is not a subcode of
the ZpZp^2..Zp^s-additive code D.
}
    return not (C subset D);

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: 'in'                                                       */
/* Parameters: u, C                                                          */
/* Function description: Return true if and only if the vector u belongs to  */
/*   the ZpZp^2..Zp^s-additive code C of type (a_1,..., a_s; t_1,..., t_s).  */
/*   The vector u can be given as a vector in (Z/p^s)^(a_1 +...+ a_s), where */
/*   the coordinates in positions X_i = [a_1+...+a_(i−1)+1,..., a_1+...+a_i] */
/*   are in p^(s−i)Z/i subset of Z/p^s for i in [1,...,s].                   */
/* Input parameters description:                                             */
/*   - u: An vector over Z/p^s                                               */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - True if u is in C, and false otherwise                                */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<ModTupRngElt> u, <MixZpCode> C) -> BoolElt                   */
/*                                                                           */
/*****************************************************************************/
intrinsic 'in'(u::ModTupRngElt, C::MixZpCode) -> BoolElt
{
Return true if and only if the vector u belongs to the ZpZp^2..Zp^s-additive
code C of type (a_1,..., a_s; t_1,..., t_s). The vector u can be given either
as a vector in (Z/p^s)^(a_1 +...+ a_s), where the coordinates in positions X_i =
[a_1+...+a_(i−1)+1,..., a_1+...+a_i] are in p^(s−i)Z/i subset of Z/p^s for i
in [1,...,s]; or as a tuple in the cartesian product set Zp^a_1 x (Zp^2)^a_2 x
.. x (Zp^s)^a_s.
}
    coercible, _ := IsCoercible(C, u);

    return coercible;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: 'in'                                                       */
/* Parameters: u, C                                                          */
/* Function description: Return true if and only if the vector u belongs to  */
/*   the ZpZp^2..Zp^s-additive code C of type (a_1,..., a_s; t_1,.., t_s).   */
/*   The vector u can be given as a tuple in the cartesian product set       */
/*   Zp^(a_1) × (Zp^2)^(a_2) ×...× (Zp^s)^(a_s).                             */
/* Input parameters description:                                             */
/*   - u: A vector over Z/p^s represented as a tuple                         */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - True if u is in C, and false otherwise                                */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<Tup> u, <MixZpCode> C) -> BoolElt                            */
/*                                                                           */
/*****************************************************************************/
intrinsic 'in'(u::Tup, C::MixZpCode) -> BoolElt
{
Return true if and only if the vector u belongs to the ZpZp^2..Zp^s-additive
code C of type (a_1,..., a_s; t_1,..., t_s). The vector u can be given either
as a vector in (Z/p^s)^(a_1 +...+ a_s), where the coordinates in positions X_i =
[a_1+...+a_(i−1)+1,..., a_1+...+a_i] are in p^(s−i)Z/i subset of Z/p^s for i
in [1,...,s]; or as a tuple in the cartesian product set Zp^a_1 x (Zp^2)^a_2 x
.. x (Zp^s)^a_s.
}
    p := #C`BaseRing;
    s := #C`LengthSeq;
    require s eq #u: "Argument 1 must be a tuple with the proper number of components";
    for i in [1..s] do
        require Type(u[i]) cmpeq ModTupRngElt:
            "Argument 1 must be a tuple containg vectors over a ring";
        require BaseRing(u[i]) cmpeq Integers(p^i):
            "The i-th component vector in the tuple must be over the ring Z/p^i";
        require Degree(u[i]) eq C`LengthSeq[i]:
            "The i-th component vector in the tuple must have the proper length";
    end for;

    coercible, _ := IsCoercible(C, FromMixZptoZps(u, p));

    return coercible;

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: 'notin'                                                    */
/* Parameters: u, C                                                          */
/* Function description: Return true if and only if the vector u does not    */
/*   belong to the ZpZp^2..Zp^s-additive code C of type (a_1,..., a_s; t_1,  */
/*   ..., t_s). The vector u can be given as a vector in (Zp^s)^(a_1 +...+   */
/*   a_s)_p^s, where the coordinates in positions X_i = [a_1+...+a_(i−1)+1,  */
/*   ..., a_1+...+a_i] are in p^(s−i)Z/i a subset of Zp^s for i in [1,...,s].*/
/* Input parameters description:                                             */
/*   - u: A vector over Z/p^s                                                */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - True if u is not in C, and false otherwise                            */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<ModTupRngElt> u, <MixZpCode> C) -> BoolElt                   */
/*                                                                           */
/*****************************************************************************/
intrinsic 'notin'(u::ModTupRngElt, C::MixZpCode) -> BoolElt
{
Return true if and only if the vector u does not belongs to the ZpZp^2..Zp^s-additive
code C of type (a_1,..., a_s; t_1,..., t_s). The vector u can be given either
as a vector in (Z/p^s)^(a_1 +...+ a_s), where the coordinates in positions X_i =
[a_1+...+a_(i−1)+1,..., a_1+...+a_i] are in p^(s−i)Z/i subset of Z/p^s for i
in [1,...,s]; or as a tuple in the cartesian product set Zp^a_1 x (Zp^2)^a_2 x
.. x (Zp^s)^a_s.
}
    return not (u in C);

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: 'notin'                                                    */
/* Parameters: u, C                                                          */
/* Function description: Return true if and only if the vector u does not    */
/*   belong to the ZpZp^2..Zp^s-additive code C of type (a_1,..., a_s; t_1,  */
/*   ..., t_s). The vector u can be given as a tuple in the cartesian product*/
/*   set Zp^(a_1) × (Zp^2)^(a_2) ×...× (Zp^s)^(a_s).                         */
/* Input parameters description:                                             */
/*   - u: A vector over Z/p^s represented as a tuple                         */
/*   - C: A ZpZp^2..Zp^s-additive code                                       */
/* Output parameters description:                                            */
/*   - True if u is not in C, and false otherwise                            */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<Tup> u, <MixZpCode> C) -> BoolElt                            */
/*                                                                           */
/*****************************************************************************/
intrinsic 'notin'(u::Tup, C::MixZpCode) -> BoolElt
{
Return true if and only if the vector u does not belongs to the ZpZp^2..Zp^s-additive
code C of type (a_1,..., a_s; t_1,..., t_s). The vector u can be given either
as a vector in (Z/p^s)^(a_1 +...+ a_s), where the coordinates in positions X_i =
[a_1+...+a_(i−1)+1,..., a_1+...+a_i] are in p^(s−i)Z/i subset of Z/p^s for i
in [1,...,s]; or as a tuple in the cartesian product set Zp^a_1 x (Zp^2)^a_2 x
.. x (Zp^s)^a_s.
}
    return not (u in C);

end intrinsic;

/*****************************************************************************/
/*                                                                           */
/* Function name: IsZero                                                     */
/* Parameters: u                                                             */
/* Function description: Return true if and only if the codeword u is the    */
/*   zero vector. The codeword u can be given either as a vector in          */
/*   (Z/p^s)^(a_1+...+ a_s) or as a tuple in the cartesian product set       */
/*   (Zp)^a_1 × (Zp^2)^a_2 ×...× (Zp^s)^a_s.                                 */
/* Input parameters description:                                             */
/*   - u: A vector over Z/p^s represented as a tuple                         */
/* Output parameters description:                                            */
/*   - True if u is the zero vector, and false otherwise                     */
/*                                                                           */
/* Function developed by Hui Hong Wu                                         */
/*                                                                           */
/* Signature: (<Tup> u) -> BoolElt                                           */
/*                                                                           */
/*****************************************************************************/
intrinsic IsZero(u::Tup) -> BoolElt
{
Return true if and only if the codeword u is the zero vector. The codeword u can
be given either as a vector in (Zp^s)^(a_1+...+ a_s) or as a tuple in the cartesian
product set (Zp)^a_1 × (Zp^2)^a_2 ×...× (Zp^s)^a_s.
}
    p := #BaseRing(u[1]);
    require IsPrime(p):
        "The first vector in the tuple must be over Z/p, with p prime";

    for i in [1..#u] do
        require Type(u[i]) cmpeq ModTupRngElt:
            "Argument 1 must be a tuple containing vectors over a ring";
        require BaseRing(u[i]) cmpeq Integers(p^i):
            "The i-th component vector in the tuple must be over the ring Z/p^i";
        if not IsZero(u[i]) then
            return false;
        end if;
    end for;

    return true;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////            CONSTRUCTION OF CODEWORD                             ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*****************************************************************************/
/*                                                                           */
/* Function name: Random                                                     */
/* Parameters: C                                                             */
/* Function description: Given a ZpZp^2...Zp^s-additive code C of type       */
/*   (a_1,...,a_s; t_1,...,t_s), which is represented as a subspace of       */
/*   (Zp^s)^n with n=a_1+...+a_n, return a random codeword of C, which is a  */
/*   vector in (Zp^s)^n where the coordinates in positions Xi = [a_1+...+    */
/*   a_(i-1)+1,...,a_1+...+a_s] are multiplied by p^(s-1) for i in [1,...,s].*/
/* Input parameters description:                                             */
/*   - C: A ZpZp^2...Zp^s-additive code                                      */
/* Output parameters description:                                            */
/*   - A random codeword of the ZpZp^2...Zp^s-additive code C                */
/*                                                                           */
/* Signature: (<MixZpCode> C) -> ModTupRngElt                                */
/*                                                                           */
/*****************************************************************************/
intrinsic Random(C::MixZpCode) -> ModTupRngElt
{
Given a ZpZp^2...Zp^s-additive code C of type (a_1,...,a_s; t_1,...,t_s), which
is represented as a subspace of (Zp^s)^n with n=a_1+...+a_n, return a random
codeword of C, which is a vector in (Zp^s)^n where the coordinates in positions
Xi = [a_1+...+a_(i-1)+1,...,a_1+...+a_s] are multiplied by p^(s-1) for i in
[1,...,s].
}
    return Random(C`Code);

end intrinsic;
