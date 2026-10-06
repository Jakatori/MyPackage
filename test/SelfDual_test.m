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

ip := MixZpInnerProduct(u, v, lengthSeq);

print "Mixed Inner Product:", ip;

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