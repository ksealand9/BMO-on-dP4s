R<x> := PolynomialRing(Rationals());

SolveInequalities := function(a, b, c, d, sign1, sign2, r)
    assert sign1 in {-1,1} and sign2 in {-1,1};
    det := a*d - b*c;
    assert det ne 0;
    alpha1 := Round((b-d)/det);
    alpha2 := Round((a-c)/det);
    n := 5;

    for x in [alpha1-n..alpha1+n] do
        for y in [alpha2-n..alpha2+n] do
            lhs1 := a*x + b*y;
            lhs2 := c*x + d*y;
            if ((sign1 eq 1 and lhs1 ge r) or
                (sign1 eq -1 and lhs1 le r)) and
               ((sign2 eq 1 and lhs2 ge r) or
                (sign2 eq -1 and lhs2 le r)) then
                return [x,y];
            end if;
        end for;
    end for;
    error "No solution found in the inequality search box.";
end function;

HasseMinkowski := function(Q, field)
    a1 := field!Coefficient(Q, 1, 2);
    a2 := field!Coefficient(Q, 2, 2);
    a3 := field!Coefficient(Q, 3, 2);
    a4 := field!Coefficient(Q, 4, 2);
    OK := RingOfIntegers(field);

    I := ideal<OK | OK!(2*a1*a2*a3*a4)>;
    P := [factor[1] : factor in Factorization(I)];

    // Original finite-field point construction.
    FindResiduePoint := function(Q, p, n)
        FF, map := ResidueClassField(p);
        pam := Inverse(map);
        coefficients := Coefficients(Q);
        coeffs := [map(coefficients[i]) : i in [1..4]];
        SS := [];
        T := [];
        for i in [1..4] do
            if coeffs[i] eq 0 then
                Append(~SS, i);
            else
                Append(~T, i);
            end if;
        end for;

        if #SS le 1 then
            P3<[y]> := PolynomialRing(FF, 3);
            List := [coeffs[j] : j in T | j ne n];
            Q := List[1]*y[1]^2 + List[2]*y[2]^2;
            Q +:= coeffs[n]*y[3]^2;
            S := Scheme(ProjectiveSpace(P3), Q);
            isConic, curve := IsConic(S);
            assert isConic;
            hasPoint, pt := HasRationalPoint(curve);
            assert hasPoint;
            pt := [pam(pt[i]) : i in [1..2]];
            Insert(~pt, n, 1);
            Insert(~pt, SS[1], 1);
        else
            pt := [pam(Sqrt(FF!(-coeffs[T[1]]/coeffs[T[2]]))), 1];
            for x in SS do
                Insert(~pt, x, 1);
            end for;
        end if;
        return pt;
    end function;

    // Same nonzero-coordinate search, in the same order.
    // Skip zero immediately instead of entering the remaining nested loops.
    FindCongruencePoint := function(Q1, p, val)
        r, map := quo<OK | p^val>;
        pam := Inverse(map);
        for n1 in r do
            if n1 eq 0 then continue; end if;
            for n2 in r do
                if n2 eq 0 then continue; end if;
                for n3 in r do
                    if n3 eq 0 then continue; end if;
                    for n4 in r do
                        if n4 eq 0 then continue; end if;
                        if Evaluate(Q1, [n1,n2,n3,n4]) eq 0 then
                            return [pam(n1),pam(n2),pam(n3),pam(n4)];
                        end if;
                    end for;
                end for;
            end for;
        end for;
        return [];
    end function;

    // Original local lifting and local value construction.
    LocalValue := function(p)
        Comp, map1 := Completion(OK, p);
        pam1 := Inverse(map1);
        RR, map2 := ResidueClassField(p);
        coeffs := [a1,a2,a3,a4];
        exp := 2 + 2*Valuation(map1(2));
        r, map3 := quo<OK | p^exp>;
        pam3 := Inverse(map3);

        for n in [1..4] do
            if map2(coeffs[n]) ne 0 then
                if Characteristic(RR) eq 2 then
                    pt := FindCongruencePoint(Q, p, exp);
                else
                    pt := FindResiduePoint(Q, p, n);
                end if;
                assert #pt eq 4;
                S<t> := PolynomialRing(Comp);
                N := OK!Evaluate(Q, pt);
                M := -map1(N) + map1(coeffs[n])*map1(OK!pt[n])^2;
                f := map1(coeffs[n])*t^2 - M;
                root_list := Roots(f, Comp);
                assert #root_list gt 0;
                Sort(~root_list);
                lift := root_list[1][1];
                point := <map1(pt[i]) : i in [1..4]>;
                point[n] := lift;
                firsthalf := map1(a1)*point[1]^2 + map1(a2)*point[2]^2;
                secondhalf := a3 + a4;
                if IsZero(firsthalf) then
                    return <pam3(map3(secondhalf)), Valuation(map1(secondhalf))>;
                else
                    return <pam3(map3(pam1(firsthalf))), Valuation(firsthalf)>;
                end if;
            end if;
        end for;
        error "No coefficient is a unit at this prime.";
    end function;

    A := AssociativeArray();
    for p in P do
        A[p] := LocalValue(p);
    end for;

    mp := [p^(A[p][2] + 1 + 2*Valuation(map1(2)))
           where Comp,map1 := Completion(field,p) : p in P];
    m0 := &*mp;
    mp1 := &*[p^A[p][2] : p in P];
    inft := InfinitePlaces(field);
    fhcs := [a1,a2];
    shcs := [a3,a4];

    // CRT and the original sign adjustment.
    X := [A[p][1] : p in P];
    S := ChineseRemainderTheorem(X, mp);

    RequiredSign := function(i)
        signs := [Sign(Evaluate(x,inft[i])) : x in fhcs];
        if signs eq [-1,-1] then
            return -1;
        elif signs eq [1,1] then
            return 1;
        elif [Sign(Evaluate(x,inft[i])) : x in shcs] eq [-1,-1] then
            return 1;
        else
            return -1;
        end if;
    end function;

    SignAdjustment := function()
        generators := Generators(m0);
        theta1 := generators[1];
        theta2 := generators[2];
        a := Evaluate(theta1,inft[1]);
        b := Evaluate(theta2,inft[1]);
        c := Evaluate(theta1,inft[2]);
        d := Evaluate(theta2,inft[2]);
        e := Sign(Evaluate(S,inft[1]));
        f := Sign(Evaluate(S,inft[2]));
        intprog := SolveInequalities(a,b,c,d,e*RequiredSign(1),f*RequiredSign(2),-1);
        return 1 + intprog[1]*theta1 + intprog[2]*theta2;
    end function;
    beta := SignAdjustment();

    SO := ideal<OK | S>;
    betaO := ideal<OK | beta>;
    a := SO*betaO*mp1^(-1);

    GG, map := RayClassGroup(m0, [1,2]);
    pam := Inverse(map);

    // Same arithmetic progression, bound and ray-class test.
    // Primality needs no full integer factorization; constants are cached.
    FindRayPrime := function(a, bound)
        y := Integers()!Norm(m0);
        x := Integers()!Norm(a);
        target := pam(a);
        for n in [0..bound] do
            t := x + n*y;
            if IsPrime(t) then
                prime_ideal_factorization := Factorization(ideal<OK | t>);
                for prime_ideal in prime_ideal_factorization do
                    if pam(prime_ideal[1]) eq target then
                        return prime_ideal[1];
                    end if;
                end for;
            end if;
        end for;
        error "No prime found within the original ray-class prime search bound.";
    end function;

    p0 := FindRayPrime(a,#GG);
    isPrincipal, x := IsPrincipal(p0*a^(-1));
    assert isPrincipal;
    if Evaluate(x,inft[1]) lt 0 then
        x *:= -1;
    end if;
    t := OK!(S*beta*x);

    // Original conic construction and final point check.
    P2<X,y,z> := ProjectiveSpace(field, 2);
    C1 := Conic(P2, a1*X^2 + a2*y^2 - t*z^2);
    C2 := Conic(P2, a3*X^2 + a4*y^2 + t*z^2);
    hasPoint1, pt1 := HasRationalPoint(C1);
    assert hasPoint1;
    hasPoint2, pt2 := HasRationalPoint(C2);
    assert hasPoint2;
    point := [field!pt1[1],field!pt1[2],field!pt2[1],field!pt2[2]];

    assert exists{c : c in point | c ne 0};
    assert Evaluate(Q,point) eq 0;
    return point;
end function;

//field := NumberField(x^2 - 3);
//P3<y4,y5,y6,y7> := ProjectiveSpace(field, 3);
//Q := y4^2 + 17*y5^2 + 5*y6^2 - 35*y7^2;
//Q;
//HasseMinkowski(Q,field);
