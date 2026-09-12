
// Practice Exercise 1
F<a> := GF(2, 4);
V := VectorSpace(F, 3);
v := V![1, a, a^2];

print "Vector space V:", V;
print "Vector v:", v;
print "Weight of v:", Weight(v);

quit;
