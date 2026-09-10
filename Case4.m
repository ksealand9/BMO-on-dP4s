// Case-4 representative construction, local evaluation, lifting and summation.
// This first split retains the supplied example. The dispatcher recognizes
// the general case-4 criterion, but other representatives remain to be added.
// HasseMinkowski must be defined before this file is loaded.

Case4 := function(Q3,Q4,f,data,selected : UseKnownPoint := true)
    QQ := Rationals();
    U := Parent(Q3);
    u0 := U.1; u1 := U.2; u2 := U.3; u3 := U.4; u4 := U.5;

    // The retained point solver and square-class representative belong to
    // this model. Do not silently reuse them for another case-4 surface.
    exampleQ3 := -12*u0^2 + 204*u1^2 + 408*u2^2 + 25*u3^2 - 2*u4^2;
    exampleQ4 := u0*u3 - 17*u1*u2;
    if Q3 ne exampleQ3 or Q4 ne exampleQ4 then
        error "Case 4 applies, but Case4.m currently implements only the supplied model in its original Q3,Q4 order.";
    end if;
    if #selected ne 1 then
        error "Case 4 with two linear factors is not yet implemented.";
    end if;
    i := selected[1];
    assert data[i]`degree eq 2;

    // Retain the original real quadratic factor and its coordinates.
    // Choose this valid support even if Factorisation orders the two
    // quadratic factors differently.
    realIndex := 0;
    for j in [1..#data] do
        g := data[j]`polynomial;
        if Degree(g) eq 2 then
            g /:= LeadingCoefficient(g);
            if Coefficient(g,1) eq 0 and Coefficient(g,0) eq -1/1152 then
                realIndex := j;
                break;
            end if;
        end if;
    end for;
    if realIndex eq 0 then
        error "The retained case-4 construction needs the factor T^2 - 1/1152.";
    end if;
    i := realIndex;
    assert not IsSquare(data[i]`epsilon);
    assert IsSquare(Norm(data[i]`epsilon));
    assert exists{j : j in [1..#data] |
                  j ne i and not IsSquare(data[j]`epsilon)};

    L2 := data[i]`field;
    sqy := data[i]`root;
    gram2 := data[i]`gram;
    basis2 := data[i]`basis;
    quadric := QuadraticForm(gram2);

    if UseKnownPoint then
        point := [L2 | 0,0,1,120*sqy];
    else
        diagonal,change := OrthogonalizeGram(gram2);
        assert diagonal eq change*gram2*Transpose(change);
        diagonal /:= diagonal[1,1];
        denominator := LCM([Denominator(L2!diagonal[j,j]) : j in [1..4]]);
        diagonal *:= denominator;
        diagonalPoint := HasseMinkowski(QuadraticForm(diagonal),L2);
        point := Eltseq(Vector(L2,diagonalPoint)*change);
    end if;
    assert exists{c : c in point | c ne 0};
    assert Evaluate(quadric,point) eq 0;

    // Tangent in the original five coordinates, using the same image basis.
    ambientPoint := Vector(L2,point)*basis2;
    ambientGram := data[i]`matrix;
    ambientGradient := (ambientGram + Transpose(ambientGram))*
                       Matrix(L2,5,1,Eltseq(ambientPoint));
    coefficients := [ambientGradient[j,1] : j in [1..5]];
    nonzero := [j : j in [1..5] | coefficients[j] ne 0];
    assert #nonzero gt 0;
    scale := coefficients[nonzero[1]];
    coefficients := [c/scale : c in coefficients];

    // Take the norm of the WHOLE tangent, not its individual coefficients.
    // Write ell=A+B*sqy, with sqy^2=1/1152. Then Norm(ell)=A^2-B^2/1152.
    // The factor 24^2 keeps the original numerator for the supplied point.
    A := &+[(QQ!Eltseq(coefficients[j])[1])*U.j : j in [1..5]];
    B := &+[(QQ!Eltseq(coefficients[j])[2])*U.j : j in [1..5]];
    numerator := 24^2*(A^2 - B^2/1152);
    denominator := (u4+u2)^2;

    if UseKnownPoint then
        assert numerator eq (24*u0-10*u4)^2 - 1250*u3^2;
    end if;
    assert IsSquare(data[i]`epsilon/(L2!17));
    a := QQ!17;
    X := Scheme(ProjectiveSpace(U),[Q3,Q4]);
    delta := Numerator(Discriminant(f));
    deltaFactors := Factorisation(delta);

    // Case-4 local evaluation, lifting and summation.
    // It currently evaluates ONE point per prime, as in the supplied code.
    TryLocalInvariant := function(a,b,p)
        QQ := Rationals();
        assert a ne 0;
        if a eq 17 and p eq 2 then
            return true,QQ!0;
        end if;
        required := p eq 2 select 3 else 1;
        if b eq 0 or RelativePrecision(b) lt required then
            return false,QQ!0;
        end if;
        v := Valuation(b);
        unit := b/(QQ!p)^v;
        u := (Integers()!unit) mod p^required;
        representative := u*p^(v mod 2);
        symbol := HilbertSymbol(QQ!a,QQ!representative,p);
        return true,(1-symbol)/4;
    end function;

    TryPointInvariant := function(P,p)
        if a eq 17 and p eq 2 then
            return true,QQ!0;
        end if;
        coords := Eltseq(P);
        d := Evaluate(denominator,coords);
        if d eq 0 then
            return false,QQ!0;
        end if;
        value := Evaluate(numerator,coords)/d;
        return TryLocalInvariant(a,value,p);
    end function;

    // Retain the example's prime list. This is not a general proof that
    // omitted finite places contribute zero. At infinity a=17 gives zero.
    ELSprimes := [factor[1] : factor in deltaFactors];
    primes := Setseq(Seqset(ELSprimes cat [11]));
    Sort(~primes);
    localPoints := AssociativeArray();
    invariants := AssociativeArray();
    undetermined := [Integers() | ];

    for p in primes do
        soluble,localPoint := IsLocallySoluble(X,p);
        if not soluble then
            print "No local point at prime",p;
            return false,QQ!0;
        end if;
        localPoints[p] := localPoint;
        determined,invariant := TryPointInvariant(localPoint,p);
        if determined then
            invariants[p] := invariant;
        else
            Append(~undetermined,p);
        end if;
    end for;

    precision := 10;
    maxPrecision := 80;
    while #undetermined gt 0 and precision le maxPrecision do
        remaining := [Integers() | ];
        for p in undetermined do
            localPoints[p] := LiftPoint(localPoints[p],precision : Strict := false);
            determined,invariant := TryPointInvariant(localPoints[p],p);
            if determined then
                invariants[p] := invariant;
            else
                Append(~remaining,p);
            end if;
        end for;
        undetermined := remaining;
        precision *:= 2;
    end while;

    if #undetermined gt 0 then
        print "Cannot compute the sum: unresolved primes",undetermined;
        return false,QQ!0;
    end if;

    localInvariantSum := &+[invariants[p] : p in primes];
    localInvariantSum -:= Floor(localInvariantSum);
    print "Sum of sampled local invariants (mod 1):",localInvariantSum;
    return true,localInvariantSum;
end function;
