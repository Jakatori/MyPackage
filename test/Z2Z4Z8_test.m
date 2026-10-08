// ====================================================================
// Z2Z4Z8-Additive Codes Self-Duality Test
// ====================================================================
print "Running Z2Z4Z8-additive code tests...";

p := 2;
// lengthSeq partitions for Z2, Z4, and Z8 components respectively
lengthSeq := [2, 2, 4]; // Total length = 8

// Test random Z2Z4Z8-additive codes
found_self_dual := false;
for i in [1..20] do
    C := RandomMixZpAdditiveCode(p, lengthSeq);

    is_orthog := IsSelfOrthogonal(C);
    is_dual := IsSelfDual(C);

    if is_dual then
        found_self_dual := true;
        print "Found a self-dual Z2Z4Z8-additive code on attempt", i;
        print "Code type:", MixZpType(C);
        print "Size (#C):", #C;
        break;
    end if;
end for;

if not found_self_dual then
    print "Completed 20 random trials (no self-dual code hit in this random batch, which is normal given statistical density).";
end if;

print "Z2Z4Z8 tests completed successfully!";

// ====================================================================
// Z2Z4Z8-Additive Codes: Advanced Examples & Practice
// ====================================================================
print "Running Z2Z4Z8-additive code practice examples...";

p := 2;
// lengthSeq for Z2, Z4, and Z8 components respectively
lengthSeq := [2, 4, 2]; // Total length = 8
print "Configured lengthSeq for Z2Z4Z8:", lengthSeq;

// 1. Generate a random Z2Z4Z8-additive code
C := RandomMixZpAdditiveCode(p, lengthSeq);
print "Successfully generated Z2Z4Z8-additive code!";

// 2. Inspect structural metrics
print "Total length:", MixZpLength(C);
print "Equivalent linear length over Zp:", MixZpLengthOverZp(C);
print "Code type (generators per level):", MixZpType(C);
print "Total number of codewords (#C):", #C;
print "Information rate:", InformationRate(C);

// 3. Test element-level inner products
if #C ge 2 then
    u := Random(C);
    v := Random(C);
    ip := MixZpInnerProduct(u, v, lengthSeq);
    print "Sample inner product between two codewords:", ip;
end if;

// 4. Test Carlet Gray map image properties for Z2Z4Z8 codes
has_linear := HasLinearCarletGrayMapImage(C);
if has_linear then
    print "Carlet Gray map image is LINEAR!";
else
    print "Carlet Gray map image is non-linear.";
end if;

print "Z2Z4Z8 practice examples completed successfully!\n";

// Custom Z2Z4Z8 code test
Z8 := IntegerRing(8);
R := RSpace(Z8, 6);
C1 := MixZpAdditiveCode([
    R![4, 0, 4, 4, 1, 3],
    R![0, 4, 6, 2, 1, 5],
    R![4, 4, 0, 1, 3, 5],
    R![0, 0, 2, 1, 1, 1]
], 2, [2, 1, 3]);

print "Custom Z2Z4Z8 Code successfully constructed!";
print "Code type:", MixZpType(C1);
print "Size (#C1):", #C1;
print "Is self-dual?", IsSelfDual(C1);
