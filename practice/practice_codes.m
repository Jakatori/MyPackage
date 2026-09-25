// practice/practice_codes.m
AttachSpec("MyPackage.spec");

print "Setting up Z4 rings and vector space...";
Z4 := IntegerRing(4);
V := RSpace(Z4, 5);

print "Creating code C1 from vector elements...";
C1 := Z2Z4AdditiveCode([
    V![2, 2, 1, 1, 3],
    V![0, 2, 1, 2, 1],
    V![2, 2, 2, 2, 2],
    V![2, 0, 1, 1, 1]
] : Alpha := 2);

print "Creating code C2 directly from a Matrix...";
A := Matrix(Z4, [
    [2, 2, 1, 1, 3],
    [0, 2, 1, 2, 1],
    [2, 2, 2, 2, 2],
    [2, 0, 1, 1, 1]
]);
C2 := Z2Z4AdditiveCode(A : Alpha := 2);

print "Verifying if C1 and C2 are equal:";
print Z2Z4Equal(C1, C2);