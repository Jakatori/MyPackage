// test/SelfDual_test.m

print "Testing IsSelfOrthogonal and IsSelfDual...";

// 1. Create a simple test instance over Z_4 (p=2, s=2)

R := IntegerRing(4);

lengthSeq := [0, 2]; // alpha_1=0, alpha_2=2

G := Matrix(R, [[2, 0], [0, 2]]);
C := LinearCode(G);

// Wrap the linear code into a MixZpCode
C_mix := MixZpAdditiveCode(C, 2, lengthSeq);

// The code is self-orthogonal and self-dual
assert IsSelfOrthogonal(C_mix) eq true;
assert IsSelfDual(C_mix) eq true;

print "Test 1 passed: self-orthogonal and self-dual.";


// 2. Test the mixed inner product

u := Vector(R, [1, 2]);
v := Vector(R, [2, 0]);

ip := MixZpInnerProduct(C_mix, u, v);

print "Mixed Inner Product:", ip;

// Example fix for Test 2
ip := MixZpInnerProduct(C_mix, u, v);
assert ip eq R!2;
print "Test 2 passed: mixed inner product.";


// 3. Test a self-orthogonal but non-self-dual code

G2 := Matrix(R, 1, 2, [2, 0]);
C2 := LinearCode(G2);

C2_mix := MixZpAdditiveCode(C2, 2, lengthSeq);

assert IsSelfOrthogonal(C2_mix) eq true;
assert IsSelfDual(C2_mix) eq false;

print "Test 3 passed: self-orthogonal but not self-dual.";

print "SelfDual tests passed!";

// ====================================================================
// Randomized Stress-Testing
// ====================================================================
print "Running randomized tests for mixed Zp-additive codes...";

p := 2;
lengthSeq := [4, 4];

for i in [1..10] do
    // Generate a valid random mixed Zp-additive code directly
    C_mix := RandomMixZpAdditiveCode(p, lengthSeq);

    // Verify execution stability on random codes
    _ := IsSelfOrthogonal(C_mix);
    _ := IsSelfDual(C_mix);
end for;

print "Randomized tests passed successfully!";


// ====================================================================
// Additional Examples & Package Feature Verification
// ====================================================================
print "Running additional mixed Zp-additive code examples...";

p := 2;
lengthSeq := [4, 4];

// 1. Generate a random mixed code and inspect basic properties
C := RandomMixZpAdditiveCode(p, lengthSeq);
print "Code successfully generated!";
print "Total length (sum of lengthSeq):", MixZpLength(C);
print "Equivalent linear length over Zp:", MixZpLengthOverZp(C);
print "Code type (number of generators per level):", MixZpType(C);
print "Size of the code (#C):", #C;
print "Information rate:", InformationRate(C);

// 2. Test inner product between random elements from the code
u := Random(C);
v := Random(C);
mixed_prod := MixZpInnerProduct(C, u, v);
print "Mixed Inner Product of two random elements:", mixed_prod;

// 3. Test Carlet Gray Map and its image structure
if HasLinearCarletGrayMapImage(C) then
    print "Carlet Gray map image is linear!";
    gray_img := CarletGrayMapImage(C);
    print "Number of vectors in Gray map image:", #gray_img;
else
    print "Carlet Gray map image is non-linear.";
end if;

print "Additional examples completed successfully!";

// 4. Test a code that is neither self-orthogonal nor self-dual
R4 := IntegerRing(4);
lengthSeq4 := [0, 2];

G3 := Matrix(R4, 1, 2, [1, 0]);
C3 := LinearCode(G3);
C3_mix := MixZpAdditiveCode(C3, 2, lengthSeq4);

assert IsSelfOrthogonal(C3_mix) eq false;
assert IsSelfDual(C3_mix) eq false;

print "Test 4 passed: code is neither self-orthogonal nor self-dual.";
