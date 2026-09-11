// ============================================================================
//  Case3.m
//
//  Case-3 representative construction, local evaluation and summation for
//  X = V(Q3) cap V(Q4) in P^4_Q, a smooth del Pezzo surface of degree 4.
//
//  Step (3) applies when S = V(f) subset P^1 contains three DEGREE-ONE points
//  T_0,T_1,T_2 with
//        eps_{T_i} notin Q^*2   and   eps_{T_i}*eps_{T_j} in Q^*2 ,
//  i.e. the three discriminants share one non-trivial square class eps.
//  Choosing P_i in V^smooth(Q_{T_i})(Q) and letting l_i be the linear form of
//  the tangent plane to V(Q_{T_i}) at P_i,
//
//     Br X / Br_0 X = { id, (eps,l_0/l_1), (eps,l_0/l_2), (eps,l_2/l_1) }
//                   =~ (Z/2)^2 .
//
//  Modulo squares l^{-1} = l, so the three non-trivial classes are evaluated
//  as the quaternion algebras
//        A_1 = (eps, l_0*l_1),  A_2 = (eps, l_0*l_2),  A_1+A_2 = (eps, l_1*l_2).
//  Local invariants are additive, so it is enough to track the pair
//  (inv_v(A_1), inv_v(A_2)) in (1/2 Z / Z)^2; the third class is their sum.
//
//  The record fields of `data` are the ones Case4.m already uses:
//        `degree, `polynomial, `field, `root, `gram, `basis, `matrix, `epsilon
//  For a degree-one point `field is Q (or a degree-one number field), so no
//  compositum is ever needed here -- that is only relevant for higher-degree
//  points, i.e. for step (4).
//
//  HasseMinkowski must be defined before this file is loaded.
//
//  WHAT IS AND IS NOT PROVED HERE, please read.
//   * The set of places inspected is {infinity, 2} together with the primes
//     dividing eps, disc(f) and the outer coefficients of f.  That is the
//     standard set, but this file does not verify that the omitted primes
//     contribute zero for the given integral model; supply anything else
//     through ExtraPrimes.
//   * At each prime several local points are sampled (from X itself and from
//     random hyperplane sections of X), giving a SUBSET of the true set of
//     local invariants.  Hence: finding the pair (0,0) among the achievable
//     sums does prove that these algebras obstruct nothing, whereas failing
//     to find it is evidence for an obstruction, not a proof of one.
//   * Rescaling an l_i changes each algebra by a constant class only, and by
//     reciprocity a constant class contributes zero to a global sum, so the
//     normalisations below do not affect any total.
// ============================================================================


// ------------------------------------------------------------------ helpers

Case3ToRational := function(x)
    // Coerce an element of a degree-one residue field down to Q.
    QQ := Rationals();
    coercible,y := IsCoercible(QQ,x);
    if coercible then
        return y;
    end if;
    sequence := Eltseq(x);
    assert &and[sequence[j] eq 0 : j in [2..#sequence]];
    return QQ!sequence[1];
end function;

Case3SquarefreePart := function(x)
    // A square-class representative: two rationals lie in the same class
    // exactly when they have the same squarefree part.
    QQ := Rationals();
    q := QQ!x;
    assert q ne 0;
    n := Numerator(q)*Denominator(q);          // same square class as q
    return Sign(n)*&*([Integers()|1] cat
        [factor[1] : factor in Factorisation(AbsoluteValue(n)) |
         IsOdd(factor[2])]);
end function;

Case3IsLocalSquare := function(x,p)
    // Is the rational x a square in Q_p?  Generalises the "a=17, p=2" test.
    QQ := Rationals();
    q := QQ!x;
    if q eq 0 then
        return true;
    end if;
    v := Valuation(q,p);
    if IsOdd(v) then
        return false;
    end if;
    u := q/p^v;
    n := Numerator(u)*Denominator(u);          // a p-adic unit, same class
    if p eq 2 then
        return (n mod 8) eq 1;
    end if;
    return IsSquare(GF(p)!n);
end function;

Case3PrimesOf := function(x)
    QQ := Rationals();
    q := QQ!x;
    if q eq 0 then
        return {Integers()| };
    end if;
    return {factor[1] : factor in Factorisation(AbsoluteValue(Numerator(q)))}
      join {factor[1] : factor in Factorisation(Denominator(q))};
end function;

Case3Primitive := function(F)
    // Rescale a nonzero rational form to a primitive integral one with
    // positive leading coefficient.
    assert F ne 0;
    F *:= LCM([Denominator(c) : c in Coefficients(F)]);
    F /:= GCD([Numerator(c) : c in Coefficients(F)]);
    if LeadingCoefficient(F) lt 0 then
        F *:= -1;
    end if;
    return F;
end function;


// --------------------------------------------------------------- criterion

// Every triple of degree-one points of S whose discriminants are non-squares
// in one common square class.  Two epsilons lie in the same class exactly
// when their squarefree parts agree, so sorting the degree-one points into
// classes replaces the search over Subsets(...,3).
// Returns a sequence of tuples <squarefree eps, sorted triple of indices>.
Case3Criterion := function(data)
    ZZ := Integers();
    classes := AssociativeArray();
    for i in [1..#data] do
        if data[i]`degree ne 1 then
            continue;
        end if;
        e := Case3SquarefreePart(Case3ToRational(data[i]`epsilon));
        if e eq 1 then
            continue;                          // epsilon is a square: skip
        end if;
        if not IsDefined(classes,e) then
            classes[e] := [ZZ| ];
        end if;
        Append(~classes[e],i);
    end for;
    triples := [];
    for e in Keys(classes) do
        indices := classes[e];
        if #indices lt 3 then
            continue;
        end if;
        for s in Subsets(Seqset(indices),3) do
            Append(~triples,<e,Sort(Setseq(s))>);
        end for;
    end for;
    return triples;
end function;


// ------------------------------------------------------------------- Case 3

//  selected     three indices into `data`, all of degree one
//  KnownPoints  optional [[..4 coords..],...], one per selected point, in the
//               coordinates of data[i]`gram, bypassing HasseMinkowski
//  RealPoints   optional real points of X in the five ambient coordinates,
//               needed only when eps < 0
//  ExtraPrimes  extra finite places to inspect
//  Samples      number of local points attempted per prime
//  SearchBound  if positive, look for a small rational point on X first
Case3 := function(Q3,Q4,f,data,selected :
                  KnownPoints := [],
                  RealPoints := [],
                  ExtraPrimes := [],
                  Samples := 8,
                  MaxPrecision := 80,
                  SearchBound := 0)

    QQ := Rationals();
    ZZ := Integers();
    U := Parent(Q3);
    assert Rank(U) eq 5;
    P4 := ProjectiveSpace(U);
    X := Scheme(P4,[Q3,Q4]);

    // ---------------------------------------------------- 1. the criterion
    if #selected ne 3 then
        error "Case 3 needs exactly three degree-one points of S.";
    end if;
    if not &and[data[i]`degree eq 1 : i in selected] then
        error "Case 3 needs three points of S of degree one.";
    end if;
    epsilons := [Case3SquarefreePart(Case3ToRational(data[i]`epsilon)) :
                 i in selected];
    if exists{e : e in epsilons | e eq 1} then
        error "Case 3 needs all three discriminants to be non-squares.";
    end if;
    if #Seqset(epsilons) ne 1 then
        error "Case 3 needs the three discriminants in a single square class.";
    end if;
    a := epsilons[1];                // squarefree representative of eps

    // ------------------------------------------ 2. the tangent linear forms
    tangents := [U| ];
    for k in [1..3] do
        i := selected[k];
        L := data[i]`field;
        gram := data[i]`gram;
        assert NumberOfRows(gram) eq 4 and NumberOfColumns(gram) eq 4;
        assert gram eq Transpose(gram);
        // rank exactly 4: H_{T_i} misses the vertex, so every point of
        // V(gram) lifts to a SMOOTH point of the cone V(Q_{T_i}).
        assert Determinant(gram) ne 0;
        if not IsSquare(Case3ToRational(Determinant(gram))*a) then
            print "Warning: epsilon and det(gram) differ modulo squares at",i;
        end if;
        quadric := QuadraticForm(gram);

        if k le #KnownPoints and #KnownPoints[k] eq 4 then
            point := [L| c : c in KnownPoints[k]];
        else
            diagonal,change := OrthogonalizeGram(gram);
            assert diagonal eq change*gram*Transpose(change);
            diagonal /:= diagonal[1,1];
            scaling := LCM([Denominator(L!diagonal[r,r]) : r in [1..4]]);
            diagonal *:= scaling;
            diagonalPoint := HasseMinkowski(QuadraticForm(diagonal),L);
            point := Eltseq(Vector(L,diagonalPoint)*change);
        end if;
        assert exists{c : c in point | c ne 0};
        assert Evaluate(quadric,point) eq 0;

        // Tangent plane in the original five coordinates, through the same
        // image basis that produced the Gram matrix.
        ambientPoint := Vector(L,point)*data[i]`basis;
        ambientGram := data[i]`matrix;
        ambientGradient := (ambientGram + Transpose(ambientGram))*
                           Matrix(L,5,1,Eltseq(ambientPoint));
        coefficients := [Case3ToRational(ambientGradient[j,1]) : j in [1..5]];
        assert exists{c : c in coefficients | c ne 0};   // P_i is smooth
        ell := Case3Primitive(&+[coefficients[j]*U.j : j in [1..5]]);
        assert Evaluate(ell,[Case3ToRational(c) :
                             c in Eltseq(ambientPoint)]) eq 0;
        Append(~tangents,ell);
    end for;

    if #Seqset(tangents) ne 3 then
        print "Warning: two tangent forms coincide, so the group computed",
              "below is smaller than (Z/2)^2.";
    end if;

    // Modulo squares l_i/l_j and l_i*l_j define the same class.
    generators := [tangents[1]*tangents[2],tangents[1]*tangents[3]];
    printf "Br X / Br_0 X = { id, (%o, l_0/l_1), (%o, l_0/l_2), (%o, l_2/l_1) }\n",
           a,a,a;
    for k in [1..3] do
        printf "  l_%o = %o\n",k-1,tangents[k];
    end for;

    if SearchBound gt 0 then
        try
            small := PointSearch(X,SearchBound);
            if #small gt 0 then
                print "X has the rational point",small[1],
                      "so no Brauer-Manin obstruction can exist.";
            end if;
        catch e
            print "PointSearch was unavailable for this model.";
        end try;
    end if;

    // ------------------------------------------------ 3. places to inspect
    discriminant := Discriminant(f);
    assert discriminant ne 0;         // X smooth iff f is separable
    primes := {2} join Case3PrimesOf(a)
                  join Case3PrimesOf(discriminant)
                  join Case3PrimesOf(LeadingCoefficient(f))
                  join Case3PrimesOf(Coefficient(f,0))
                  join {ZZ!p : p in ExtraPrimes};
    primes := Sort(Setseq(primes));
    print "Finite places inspected:",primes;

    // ------------------------------------------------- 4. local invariants
    Combine := function(S,T)
        result := {};
        for x in S do
            for y in T do
                Include(~result,[QQ| (x[k]+y[k]) - Floor(x[k]+y[k]) :
                                 k in [1..2]]);
            end for;
        end for;
        return result;
    end function;

    TryLocalInvariant := function(b,p)
        if Case3IsLocalSquare(a,p) then
            return true,QQ!0;                  // (a,*)_p is identically trivial
        end if;
        if Type(b) in {RngIntElt,FldRatElt} then
            if b eq 0 then
                return false,QQ!0;
            end if;
            return true,(1-HilbertSymbol(QQ!a,QQ!b,p))/4;
        end if;
        required := p eq 2 select 3 else 1;
        if b eq 0 or RelativePrecision(b) lt required then
            return false,QQ!0;                 // not enough digits to decide
        end if;
        v := Valuation(b);
        unit := b/(QQ!p)^v;
        u := (ZZ!unit) mod p^required;
        representative := u*p^(v mod 2);
        symbol := HilbertSymbol(QQ!a,QQ!representative,p);
        return true,(1-symbol)/4;
    end function;

    // The pair (inv_p(A_1),inv_p(A_2)) at one local point.  A point lying on
    // l_0 = 0 gives value 0 and is reported undetermined rather than being
    // silently assigned the invariant zero; other samples then cover it.
    TryPointInvariants := function(P,p)
        coordinates := Eltseq(P);
        result := [QQ| ];
        for F in generators do
            determined,invariant := TryLocalInvariant(Evaluate(F,coordinates),p);
            if not determined then
                return false,[QQ| ];
            end if;
            Append(~result,invariant);
        end for;
        return true,result;
    end function;

    // Local points: the one IsLocallySoluble returns for X, plus points on
    // random hyperplane sections of X, which land in different residue discs.
    SampleLocalPoints := function(p,count)
        points := [];
        soluble,localPoint := IsLocallySoluble(X,p);
        if not soluble then
            return false,points;
        end if;
        Append(~points,localPoint);
        attempts := 0;
        while #points lt count and attempts lt 6*count do
            attempts +:= 1;
            H := &+[Random(-6,6)*U.j : j in [1..5]];
            if H eq 0 then
                continue;
            end if;
            section := Scheme(P4,[Q3,Q4,H]);
            try
                if Dimension(section) eq 1 then
                    ok,sectionPoint := IsLocallySoluble(section,p);
                    if ok then
                        Append(~points,sectionPoint);
                    end if;
                end if;
            catch e
                attempts +:= 1;
            end try;
        end while;
        return true,points;
    end function;

    localSets := AssociativeArray();
    undetermined := [ZZ| ];

    for p in primes do
        soluble,samples := SampleLocalPoints(p,Samples);
        if not soluble then
            print "No local point at prime",p,": X has no adelic point.";
            return false,false,{};
        end if;
        found := {};
        for sample in samples do
            localPoint := sample;
            precision := 10;
            determined,invariants := TryPointInvariants(localPoint,p);
            while not determined and precision le MaxPrecision do
                localPoint := LiftPoint(localPoint,precision : Strict := false);
                determined,invariants := TryPointInvariants(localPoint,p);
                precision *:= 2;
            end while;
            if determined then
                Include(~found,invariants);
            end if;
        end for;
        if #found eq 0 then
            Append(~undetermined,p);
        else
            localSets[p] := found;
            printf "p = %o : sampled (inv A_1, inv A_2) = %o\n",p,found;
        end if;
    end for;

    // ------------------------------------------------------ 5. the real place
    if a gt 0 then
        realSet := {[QQ| 0,0]};        // (a,*)_infinity is trivial for a > 0
    else
        realSet := {};
        for P in RealPoints do
            coordinates := [RealField(30)| c : c in P];
            values := [Evaluate(F,coordinates) : F in generators];
            if &and[AbsoluteValue(v) gt 10^-20 : v in values] then
                Include(~realSet,[QQ| (v lt 0) select QQ!(1/2) else QQ!0 :
                                 v in values]);
            end if;
        end for;
        if #realSet eq 0 then
            print "The real place is undetermined: eps < 0 and no usable real",
                  "point of X was supplied.  Pass RealPoints := [...].";
            Append(~undetermined,-1);
        end if;
    end if;

    if #undetermined gt 0 then
        print "Cannot complete the sum: unresolved places",undetermined;
        return false,false,{};
    end if;

    // ---------------------------------------------------- 6. global sums
    // The places may be chosen independently, so the achievable global sums
    // are the sumset of the local sets.  A_1 + A_2 needs no separate test:
    // its sum is the sum of the two coordinates below.
    achievable := realSet;
    for p in primes do
        achievable := Combine(achievable,localSets[p]);
    end for;

    print "Achievable (sum inv A_1, sum inv A_2) mod 1:",achievable;
    obstruction := not [QQ| 0,0] in achievable;
    if obstruction then
        print "No sampled adelic point kills both sums, so on this evidence",
              "the Brauer-Manin obstruction is non-empty.  This is only a",
              "proof once the local sets above are known to be complete.";
    else
        print "Some adelic point has both sums zero, so these algebras give",
              "no Brauer-Manin obstruction.";
    end if;
    return true,obstruction,achievable;
end function;

