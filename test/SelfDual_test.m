// test/SelfDual_test.m
print "Testing IsSelfOrthogonalZp and IsSelfDualZp...";

// 1. Create simple test instance over Z_4 (p=2, s=2)
R := IntegerRing(4);
lengthSeq := [0, 2]; // alpha_1=0, alpha_2=2 (length 2 over Z_4)

G := Matrix(R, [[2, 0], [0, 2]]);
C := LinearCode(G);

// Wrap the linear code into a MixZpCode
C_mix := MixZpAdditiveCode(C, 2, lengthSeq);

assert IsSelfOrthogonal(C_mix) eq true;
assert IsSelfDual(C_mix) eq true;

print "SelfDual tests passed!";

// 2. Test mixed inner product
u := Vector(R, [1, 2]);
v := Vector(R, [2, 0]);
ip := MixZpInnerProduct(u, v, lengthSeq);
print "Mixed Inner Product:", ip;

// 3. Test code instance 2
G2 := Matrix(R, 1, 2, [2, 0]);
C2 := LinearCode(G2);
C2_mix := MixZpAdditiveCode(C2, 2, lengthSeq);

isOrthogonal := IsSelfOrthogonal(C2_mix);
print "Is self-orthogonal?", isOrthogonal;

isDual := IsSelfDual(C2_mix);
print "Is self-dual?", isDual;