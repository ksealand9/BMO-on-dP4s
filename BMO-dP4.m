// Run from the directory containing both files:
//     load "BMO-dP4.m";
// Not executed in Magma here.

load "Hasse--Minkowski.m";

// Keep the supplied point for this example. Set false to compute a point
// using HasseMinkowski, with a change of coordinates to diagonal form.
UseKnownPoint := true;

// Preliminary objects.
QQ := Rationals();
R<T> := PolynomialRing(QQ);
U<u0,u1,u2,u3,u4> := PolynomialRing(QQ,5);

Q4 := u0*u3 - 17*u1*u2;
Q3 := -12*u0^2 + 204*u1^2 + 408*u2^2 + 25*u3^2 - 2*u4^2;
X := Scheme(ProjectiveSpace(U),[Q3,Q4]);

// PointSearch(X,100);
// print "Is X ELS?", &and[IsLocallySoluble(X,p) : p in PrimesUpTo(100)];

// Keep the original pencil and its factor ordering.
M3 := SymmetricMatrix(Q4);
M4 := SymmetricMatrix(Q3);
f := Determinant(M3 + T*M4);
factors := Factorisation(f);
assert #factors eq 3;

print "f:", factors;
print "LC(f):", LeadingCoefficient(f);
delta := Numerator(Discriminant(f));
assert delta ne 0;
deltaFactors := Factorisation(delta);
print "Delta:", deltaFactors;

f1 := factors[1][1];
f2 := factors[2][1];
f3 := factors[3][1];
assert Degree(f2) eq 2 and Degree(f3) eq 2;

L1<rat> := quo<R | f1>;
L2<sqy> := NumberField(f2);
L3<the> := NumberField(f3);

// The same image-basis restriction, computed once for each pencil member.
PencilData := function(root,M3,M4)
    M := M3 + root*M4;
    basis := Matrix(Basis(Image(M)));
    gram := basis*M*Transpose(basis);
    assert Nrows(gram) eq 4 and Determinant(gram) ne 0;
    return gram,basis;
end function;

PrintDiscriminant := procedure(label,epsilon)
    norm := Norm(epsilon);
    print label, epsilon;
    print "  Is square?", IsSquare(epsilon);
    print "  Norm:", norm;
    print "  Is norm square?", IsSquare(norm);
end procedure;

gram1,basis1 := PencilData(rat,M3,M4);
gram2,basis2 := PencilData(sqy,M3,M4);
gram3,basis3 := PencilData(the,M3,M4);

epsilon1 := Determinant(gram1);
epsilon2 := Determinant(gram2);
epsilon3 := Determinant(gram3);
PrintDiscriminant("epsilon1:",epsilon1);
PrintDiscriminant("epsilon2:",epsilon2);
PrintDiscriminant("epsilon3:",epsilon3);

// A point on the four-variable quadric from the second factor.
quadric := QuadraticForm(gram2);
print "Quadric:", quadric;

if UseKnownPoint then
    point := [L2 | 0,0,1,120*sqy];
else
    // HasseMinkowski expects a diagonal form. Magma returns
    // diagonal = change*gram2*Transpose(change).
    diagonal,change := OrthogonalizeGram(gram2);
    assert diagonal eq change*gram2*Transpose(change);

    // Normalize the first coefficient, then clear denominators.
    // Scaling the whole equation does not change its projective points.
    diagonal /:= diagonal[1,1];
    denominator := LCM([Denominator(L2!diagonal[i,i]) : i in [1..4]]);
    diagonal *:= denominator;
    diagonalQuadric := QuadraticForm(diagonal);
    diagonalPoint := HasseMinkowski(diagonalQuadric,L2);

    // Return to the coordinates of quadric before computing its tangent.
    point := Eltseq(Vector(L2,diagonalPoint)*change);
end if;

assert exists{c : c in point | c ne 0};
assert Evaluate(quadric,point) eq 0;
print "Point:", point;

// Tangent hyperplane in the four reduced coordinates.
P3<v0,v1,v2,v3> := ProjectiveSpace(L2,3);
coordinates := [v0,v1,v2,v3];
pointColumn := Matrix(L2,4,1,point);
gradient := (gram2 + Transpose(gram2))*pointColumn;
tangentForm := &+[gradient[i,1]*(coordinates[i]-point[i]) : i in [1..4]];
print "Tangent form (reduced coordinates):", tangentForm;

// The same tangent in the original five coordinates, via the image basis.
ambientPoint := Vector(L2,point)*basis2;
ambientGram := M3 + sqy*M4;
ambientGradient := (ambientGram + Transpose(ambientGram))*
                   Matrix(L2,5,1,Eltseq(ambientPoint));
P4<o0,o1,o2,o3,o4> := ProjectiveSpace(L2,4);
ambientCoordinates := [o0,o1,o2,o3,o4];
ambientTangent := &+[ambientGradient[i,1]*ambientCoordinates[i] : i in [1..5]];
print "Tangent form (original coordinates):", ambientTangent;

// Sample Hilbert-symbol evaluations for the original expression.
// This expression is supplied separately: it is not derived automatically
// from the tangent above, and one sample per prime does not establish a BMO.
ELSprimes := [factor[1] : factor in deltaFactors];
print "Primes dividing the numerator of Delta:", ELSprimes;

numerator := (3*u0-5*u3)^2 - 2*u2^2;
denominator := (u4+u2)^2;
expr := numerator/denominator;

for p in ELSprimes cat [11] do
    soluble,localPoint := IsLocallySoluble(X,p);
    assert soluble;
    print "p:", p, "point:", localPoint;

    localCoordinates := Eltseq(localPoint);
    denominatorValue := Evaluate(denominator,localCoordinates);
    assert denominatorValue ne 0;
    
    value := Evaluate(numerator,localCoordinates)/denominatorValue;
    assert value ne 0;
    
    symbol := HilbertSymbol(QQ!17,QQ!value,p);
    print "Hilbert symbol:", symbol;
end for;
