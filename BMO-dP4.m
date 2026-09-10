load "Hasse--Minkowski.m";
load "Case4.m";

// Return convention: true,sum means the sampled finite-place sum was
// determined (or the Brauer quotient is trivial). It does NOT certify a BMO.
// false,0 means the sample calculation was unsuccessful; ignore the 0.
// Case 3 and unimplemented case-4 representatives raise explicit errors.
BMO := function(Q3,Q4 : UseKnownPoint := true)
    QQ := Rationals();
    U := Parent(Q3);
    assert Parent(Q4) eq U;
    assert BaseRing(U) eq QQ and Rank(U) eq 5;
    R<T> := PolynomialRing(QQ);

    M3 := SymmetricMatrix(Q4);
    M4 := SymmetricMatrix(Q3);
    f := Determinant(M3 + T*M4);
    assert f ne 0;

    // Include a possible singular pencil member at infinity by choosing
    // a nonsingular M4. This changes the pencil parameter, not X.
    if Degree(f) lt 5 then
        for c in [0..5] do
            if Determinant(M4 + c*M3) ne 0 then
                M4 +:= c*M3;
                break;
            end if;
        end for;
        f := Determinant(M3 + T*M4);
    end if;
    assert Degree(f) eq 5;
    assert Discriminant(f) ne 0;

    factorisation := Factorisation(f);
    factorDegrees := [Degree(t[1]) : t in factorisation];

    // Step (2).
    if 5 in factorDegrees or 4 in factorDegrees then
        print "Br(X)/Br_0(X) is trivial.";
        return true,QQ!0;
    end if;

    // Compute the same image-basis restrictions as in the original code.
    DataFormat := recformat<polynomial,degree,field,root,matrix,gram,basis,epsilon>;
    data := [* *];
    for factor in factorisation do
        g := factor[1];
        d := Degree(g);
        if d eq 1 then
            K := QQ;
            root := -Coefficient(g,0)/Coefficient(g,1);
        else
            K<root> := NumberField(g);
        end if;
        M := ChangeRing(M3,K) + root*ChangeRing(M4,K);
        assert Rank(M) eq 4;
        basis := Matrix(Basis(Image(M)));
        gram := basis*M*Transpose(basis);

        // Fallback if the image is not a nondegenerate complement.
        if Determinant(gram) eq 0 then
            for omitted in [1..5] do
                indices := [i : i in [1..5] | i ne omitted];
                basis := Matrix(K,4,5,[i eq j select 1 else 0
                                      : i in indices, j in [1..5]]);
                gram := basis*M*Transpose(basis);
                if Determinant(gram) ne 0 then
                    break;
                end if;
            end for;
        end if;
        assert Determinant(gram) ne 0;
        Append(~data,rec<DataFormat |
            polynomial := g, degree := d, field := K, root := root,
            matrix := M, gram := gram, basis := basis,
            epsilon := Determinant(gram)
        >);
    end for;

    linear := [i : i in [1..#data] | data[i]`degree eq 1];
    quadratic := [i : i in [1..#data] | data[i]`degree eq 2];
    nonsquare := [not IsSquare(data[i]`epsilon) : i in [1..#data]];

    // Step (3) takes precedence over step (4).
    for triple in Subsets(Seqset(linear),3) do
        indices := Setseq(triple);
        i := indices[1]; j := indices[2]; k := indices[3];
        if nonsquare[i] and nonsquare[j] and nonsquare[k]
           and IsSquare(data[i]`epsilon*data[j]`epsilon)
           and IsSquare(data[i]`epsilon*data[k]`epsilon) then
            error "Case 3 applies: Case3.m has not yet been implemented.";
        end if;
    end for;

    // Step (4): total degree two, hence one quadratic or two linears.
    candidates := [* *];
    for i in quadratic do
        Append(~candidates,[i]);
    end for;
    for pair in Subsets(Seqset(linear),2) do
        Append(~candidates,Setseq(pair));
    end for;

    selected := [Integers() | ];
    for candidate in candidates do
        if not (&and[nonsquare[i] : i in candidate]) then
            continue;
        end if;
        normProduct := QQ!1;
        for i in candidate do
            if data[i]`degree eq 1 then
                normProduct *:= QQ!data[i]`epsilon;
            else
                normProduct *:= QQ!Norm(data[i]`epsilon);
            end if;
        end for;
        if IsSquare(normProduct) and
           exists{j : j in [1..#data] | j notin candidate and nonsquare[j]} then
            selected := candidate;
            break;
        end if;
    end for;

    // Step (5).
    if #selected eq 0 then
        print "Br(X)/Br_0(X) is trivial.";
        return true,QQ!0;
    end if;

    // Case4 owns the representative construction and the local calculation.
    determined,total := Case4(Q3,Q4,f,data,selected :
                             UseKnownPoint := UseKnownPoint);
    return determined,total;
end function;

// Example (run these lines yourself; loading the file runs no example):
// U<u0,u1,u2,u3,u4> := PolynomialRing(Rationals(),5);
// Q3 := -12*u0^2 + 204*u1^2 + 408*u2^2 + 25*u3^2 - 2*u4^2;
// Q4 := u0*u3 - 17*u1*u2;
// determined,total := BMO(Q3,Q4);
