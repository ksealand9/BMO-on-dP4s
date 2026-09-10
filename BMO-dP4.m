load "Hasse--Minkowski.m";

// Keep the supplied point for this example. Set false to compute a point
// using HasseMinkowski, with a change of coordinates to diagonal form.
load "Hasse--Minkowski.m";

// Keep the supplied point for this example. Set false to compute a point
// using HasseMinkowski, with a change of coordinates to diagonal form.
UseKnownPoint := true;

// Preliminary objects.
QQ := Rationals();
R<T> := PolynomialRing(QQ);
U<u0,u1,u2,u3,u4> := PolynomialRing(QQ,5);

//Q4 := u0*u3 - 17*u1*u2;
//Q3 := -12*u0^2 + 204*u1^2 + 408*u2^2 + 25*u3^2 - 2*u4^2;

BMO := function(Q3,Q4 : UseKnownPoint := true)
    assert Parent(Q3) eq U and Parent(Q4) eq U;
    assert BaseRing(U) eq QQ and Rank(U) eq 5;
    
X := Scheme(ProjectiveSpace(U),[Q3,Q4]);

// PointSearch(X,100);
// print "Is X ELS?", &and[IsLocallySoluble(X,p) : p in PrimesUpTo(100)];

// Keep the original pencil and its factor ordering.
M3 := SymmetricMatrix(Q4);
M4 := SymmetricMatrix(Q3);
f := Determinant(M3 + T*M4);

factorisation := Factorisation(f);

assert &and[
    factor[2] eq 1 : factor in factorisation
];

factorDegrees := [Degree(factor[1]) : factor in factorisation];
Sort(~factorDegrees);

print "Factorisation degrees:", factorDegrees;

delta := Numerator(Discriminant(f));
assert delta ne 0;
deltaFactors := Factorisation(delta);

IndicesOfDegree := function(factorisation,d)
    return [i : i in [1..#factorisation]
              | Degree(factorisation[i][1]) eq d];
end function;

if factorDegrees eq [5] or factorDegrees eq [1,4] then
    print "Br(X)/Br(Q) is trivial.";
    return true, Rationals()!0;
end if;

if factorDegrees ne [1,2,2]
   and factorDegrees ne [2,3]
   and factorDegrees ne [1,1,1,2]
   and factorDegrees ne [1,1,1,1,1] then

    error "Factorisation pattern not yet implemented.";
end if;

assert factorDegrees eq [1,2,2];

i1 := IndicesOfDegree(factorisation,1)[1];
quadraticIndices := IndicesOfDegree(factorisation,2);

i2 := quadraticIndices[1];
i3 := quadraticIndices[2];

f1 := factorisation[i1][1];
f2 := factorisation[i2][1];
f3 := factorisation[i3][1];

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

gram1,basis1 := PencilData(rat,M3,M4);
gram2,basis2 := PencilData(sqy,M3,M4);
gram3,basis3 := PencilData(the,M3,M4);

epsilon1 := Determinant(gram1);
epsilon2 := Determinant(gram2);
epsilon3 := Determinant(gram3);

// A point on the four-variable quadric from the second factor.
quadric := QuadraticForm(gram2);

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

// Tangent hyperplane in the four reduced coordinates.
P3<v0,v1,v2,v3> := ProjectiveSpace(L2,3);
coordinates := [v0,v1,v2,v3];
pointColumn := Matrix(L2,4,1,point);
gradient := (gram2 + Transpose(gram2))*pointColumn;
tangentForm := &+[gradient[i,1]*(coordinates[i]-point[i]) : i in [1..4]];

// The same tangent in the original five coordinates, via the image basis.
ambientPoint := Vector(L2,point)*basis2;
ambientGram := M3 + sqy*M4;
ambientGradient := (ambientGram + Transpose(ambientGram))*
                   Matrix(L2,5,1,Eltseq(ambientPoint));
P4<o0,o1,o2,o3,o4> := ProjectiveSpace(L2,4);
ambientCoordinates := [o0,o1,o2,o3,o4];
ambientTangent := &+[ambientGradient[i,1]*ambientCoordinates[i] : i in [1..5]];

// Sample Hilbert-symbol evaluations for the tangent-norm representative.
// The explicit formula below uses the supplied point, whose tangent is
// ell = u0 + 50*sqy*u3 - (5/12)*u4, with sqy^2=1/1152.
// Its numerator is Norm(24*ell); 24^2 is a rational square.
// This remains a sampling loop, not a full computation of the BMO.

// First layer: a precision-aware local invariant for (a,b) over Q_p.
// a is an exact nonzero rational; b is a finite-precision element of Q_p
// (not an extension of Q_p). Returns success and an invariant in {0,1/2}.
// On failure the second return value is a placeholder and MUST be ignored.
// These precision bounds are sufficient, not necessarily optimal for a given a.
TryLocalInvariant := function(a,b,p)
    QQ := Rationals();
    assert a ne 0;
    // For this example the algebra splits at 2, independently of b.
    if a eq 17 and p eq 2 then
        return true,QQ!0;
    end if;
    required := p eq 2 select 3 else 1;

    if b eq 0 then
        return false,QQ!0;
    end if;
    if RelativePrecision(b) lt required then
        return false,QQ!0;
    end if;

    // The square class is determined by valuation parity and the unit part
    // modulo p (odd p), or modulo 8 (p=2).
    v := Valuation(b);
    unit := b/(QQ!p)^v;
    u := (Integers()!unit) mod p^required;
    representative := u*p^(v mod 2);
    symbol := HilbertSymbol(QQ!a,QQ!representative,p);
    return true,(1-symbol)/4;
end function;

ELSprimes := [factor[1] : factor in deltaFactors];

numerator := (24*u0-10*u4)^2 - 1250*u3^2;
denominator := (u4+u2)^2;
expr := numerator/denominator;

// Evaluate the fixed class at one local point, keeping unresolved values separate.
TryPointInvariant := function(P,p)
    if p eq 2 then
        return true,Rationals()!0;  // 17 is a square in Q_2.
    end if;
    coords := Eltseq(P);
    d := Evaluate(denominator,coords);
    if d eq 0 then
        return false,Rationals()!0;
    end if;
    value := Evaluate(numerator,coords)/d;
    return TryLocalInvariant(17,value,p);
end function;

localPoints := AssociativeArray();
invariants := AssociativeArray();
undetermined := [Integers() | ];

// First pass: keep the points, the known invariants, and unresolved primes.
for p in ELSprimes cat [11] do
    soluble,localPoint := IsLocallySoluble(X,p);
    assert soluble;
    localPoints[p] := localPoint;
    determined,invariant := TryPointInvariant(localPoint,p);
    if determined then
        invariants[p] := invariant;
    else
        Append(~undetermined,p);;
    end if;
end for;

// Refine only unresolved points. These are requested precisions: Strict:=false
// permits a lower achieved precision when limited by the ambient local field.
// Always let TryLocalInvariant check the precision actually obtained.
precision := 10;
maxPrecision := 80;
while #undetermined gt 0 and precision le maxPrecision do
    remaining := [Integers() | ];

    for p in undetermined do
        localPoints[p] := LiftPoint(localPoints[p],precision : Strict := false);
        determined,invariant := TryPointInvariant(localPoints[p],p);
        if determined then
            invariants[p] := invariant;
            print "p:", p, "local invariant:", invariant;
        else
            Append(~remaining,p);
            print "p:", p, "still undetermined";
        end if;
    end for;

    undetermined := remaining;
    precision *:= 2;
end while;

if #undetermined gt 0 then
    print "Cannot compute the sum: unresolved primes", undetermined;
else
    localInvariantSum := &+[invariants[p] : p in Keys(invariants)];
    localInvariantSum -:= Floor(localInvariantSum);

    print "Sum of local invariants (mod 1):", localInvariantSum;

    if localInvariantSum ne 0 then
        print "There is a Brauer--Manin obstruction.";
    else
        print "There is no Brauer--Manin obstruction.";
    end if;
end if;

    return true, localInvariantSum;
end function;


// Preliminary objects.
QQ := Rationals();
R<T> := PolynomialRing(QQ);
U<u0,u1,u2,u3,u4> := PolynomialRing(QQ,5);

BMO := function(Q3,Q4 : UseKnownPoint := true)
    assert Parent(Q3) eq U and Parent(Q4) eq U;
    assert BaseRing(U) eq QQ and Rank(U) eq 5;
    
X := Scheme(ProjectiveSpace(U),[Q3,Q4]);

// PointSearch(X,100);
// print "Is X ELS?", &and[IsLocallySoluble(X,p) : p in PrimesUpTo(100)];

// Keep the original pencil and its factor ordering.
M3 := SymmetricMatrix(Q4);
M4 := SymmetricMatrix(Q3);
f := Determinant(M3 + T*M4);

factorisation := Factorisation(f);

assert &and[
    factor[2] eq 1 : factor in factorisation
];

factorDegrees := [Degree(factor[1]) : factor in factorisation];
Sort(~factorDegrees);

print "Factorisation degrees:", factorDegrees;

delta := Numerator(Discriminant(f));
assert delta ne 0;
deltaFactors := Factorisation(delta);

IndicesOfDegree := function(factorisation,d)
    return [i : i in [1..#factorisation]
              | Degree(factorisation[i][1]) eq d];
end function;

if factorDegrees eq [5] or factorDegrees eq [1,4]
   or factorDegrees eq [1,1,3] then

    print "Br(X)/Br(Q) is trivial.";
    return true, Rationals()!0;
end if;

if factorDegrees ne [1,2,2]
   and factorDegrees ne [2,3]
   and factorDegrees ne [1,1,1,2]
   and factorDegrees ne [1,1,1,1,1] then

    error "Factorisation pattern not yet implemented.";
end if;

assert factorDegrees eq [1,2,2];

i1 := IndicesOfDegree(factorisation,1)[1];
quadraticIndices := IndicesOfDegree(factorisation,2);

i2 := quadraticIndices[1];
i3 := quadraticIndices[2];

f1 := factorisation[i1][1];
f2 := factorisation[i2][1];
f3 := factorisation[i3][1];

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

gram1,basis1 := PencilData(rat,M3,M4);
gram2,basis2 := PencilData(sqy,M3,M4);
gram3,basis3 := PencilData(the,M3,M4);

epsilon1 := Determinant(gram1);
epsilon2 := Determinant(gram2);
epsilon3 := Determinant(gram3);

// A point on the four-variable quadric from the second factor.
quadric := QuadraticForm(gram2);

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

// Tangent hyperplane in the four reduced coordinates.
P3<v0,v1,v2,v3> := ProjectiveSpace(L2,3);
coordinates := [v0,v1,v2,v3];
pointColumn := Matrix(L2,4,1,point);
gradient := (gram2 + Transpose(gram2))*pointColumn;
tangentForm := &+[gradient[i,1]*(coordinates[i]-point[i]) : i in [1..4]];

// The same tangent in the original five coordinates, via the image basis.
ambientPoint := Vector(L2,point)*basis2;
ambientGram := M3 + sqy*M4;
ambientGradient := (ambientGram + Transpose(ambientGram))*
                   Matrix(L2,5,1,Eltseq(ambientPoint));
P4<o0,o1,o2,o3,o4> := ProjectiveSpace(L2,4);
ambientCoordinates := [o0,o1,o2,o3,o4];
ambientTangent := &+[ambientGradient[i,1]*ambientCoordinates[i] : i in [1..5]];

// Sample Hilbert-symbol evaluations for the tangent-norm representative.
// The explicit formula below uses the supplied point, whose tangent is
// ell = u0 + 50*sqy*u3 - (5/12)*u4, with sqy^2=1/1152.
// Its numerator is Norm(24*ell); 24^2 is a rational square.
// This remains a sampling loop, not a full computation of the BMO.

// First layer: a precision-aware local invariant for (a,b) over Q_p.
// a is an exact nonzero rational; b is a finite-precision element of Q_p
// (not an extension of Q_p). Returns success and an invariant in {0,1/2}.
// On failure the second return value is a placeholder and MUST be ignored.
// These precision bounds are sufficient, not necessarily optimal for a given a.
TryLocalInvariant := function(a,b,p)
    QQ := Rationals();
    assert a ne 0;
    // For this example the algebra splits at 2, independently of b.
    if a eq 17 and p eq 2 then
        return true,QQ!0;
    end if;
    required := p eq 2 select 3 else 1;

    if b eq 0 then
        return false,QQ!0;
    end if;
    if RelativePrecision(b) lt required then
        return false,QQ!0;
    end if;

    // The square class is determined by valuation parity and the unit part
    // modulo p (odd p), or modulo 8 (p=2).
    v := Valuation(b);
    unit := b/(QQ!p)^v;
    u := (Integers()!unit) mod p^required;
    representative := u*p^(v mod 2);
    symbol := HilbertSymbol(QQ!a,QQ!representative,p);
    return true,(1-symbol)/4;
end function;

ELSprimes := [factor[1] : factor in deltaFactors];

numerator := (24*u0-10*u4)^2 - 1250*u3^2;
denominator := (u4+u2)^2;
expr := numerator/denominator;

// Evaluate the fixed class at one local point, keeping unresolved values separate.
TryPointInvariant := function(P,p)
    if p eq 2 then
        return true,Rationals()!0;  // 17 is a square in Q_2.
    end if;
    coords := Eltseq(P);
    d := Evaluate(denominator,coords);
    if d eq 0 then
        return false,Rationals()!0;
    end if;
    value := Evaluate(numerator,coords)/d;
    return TryLocalInvariant(17,value,p);
end function;

localPoints := AssociativeArray();
invariants := AssociativeArray();
undetermined := [Integers() | ];

// First pass: keep the points, the known invariants, and unresolved primes.
for p in ELSprimes cat [11] do
    soluble,localPoint := IsLocallySoluble(X,p);
    assert soluble;
    localPoints[p] := localPoint;
    determined,invariant := TryPointInvariant(localPoint,p);
    if determined then
        invariants[p] := invariant;
    else
        Append(~undetermined,p);;
    end if;
end for;

// Refine only unresolved points. These are requested precisions: Strict:=false
// permits a lower achieved precision when limited by the ambient local field.
// Always let TryLocalInvariant check the precision actually obtained.
precision := 10;
maxPrecision := 80;
while #undetermined gt 0 and precision le maxPrecision do
    remaining := [Integers() | ];

    for p in undetermined do
        localPoints[p] := LiftPoint(localPoints[p],precision : Strict := false);
        determined,invariant := TryPointInvariant(localPoints[p],p);
        if determined then
            invariants[p] := invariant;
            print "p:", p, "local invariant:", invariant;
        else
            Append(~remaining,p);
            print "p:", p, "still undetermined";
        end if;
    end for;

    undetermined := remaining;
    precision *:= 2;
end while;

if #undetermined gt 0 then
    print "Cannot compute the sum: unresolved primes", undetermined;
else
    localInvariantSum := &+[invariants[p] : p in Keys(invariants)];
    localInvariantSum -:= Floor(localInvariantSum);

    print "Sum of local invariants (mod 1):", localInvariantSum;

    if localInvariantSum ne 0 then
        print "There is a Brauer--Manin obstruction.";
    else
        print "There is no Brauer--Manin obstruction.";
    end if;
end if;

    return true, localInvariantSum;
end function;
