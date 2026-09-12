// practice/exercise2.m: Linear Codes and Generator Matrices

// 1. Define the base field GF(2)
F := GF(2);

// 2. Define a Generator Matrix (3 rows, 6 columns over GF(2))
G := Matrix(F, [
    [1, 0, 0, 1, 1, 0],
    [0, 1, 0, 1, 0, 1],
    [0, 0, 1, 0, 1, 1]
]);

// 3. Construct the Linear Code C from the Generator Matrix
C := LinearCode(G);

print "=== Linear Code C ===";
print C;
print "Length (n):", Length(C);
print "Dimension (k):", Dimension(C);
print "Minimum Distance (d):", MinimumDistance(C);

// 4. Extract Parity Check Matrix and Dual Code
H := ParityCheckMatrix(C);
C_dual := Dual(C);

print "\n=== Parity Check Matrix H ===";
print H;

print "\n=== Dual Code C_dual ===";
print C_dual;

// 5. Weight Enumerator
print "\n=== Complete Weight Enumerator ===";
print WeightEnumerator(C);

quit;