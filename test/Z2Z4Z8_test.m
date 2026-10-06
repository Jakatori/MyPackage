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