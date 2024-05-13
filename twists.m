freeze;

declare verbose Twists, 1;
import "AutStrataChar0Equations.m" : GeometricAutomorphismGroup;

function ApplyGalois(f, rho)
	assert Type(f) eq AlgMatElt;
	// Given a matrix, apply a Galois action on its coefficients.
	return Matrix([ [rho(f[j][i]) : i in [1..NumberOfRows(f)]] : j in [1..NumberOfColumns(f)]]);
end function;

function MapToAssociativeArray(M)
	// Turn a map (recursively) into an associative array in order to not recompute the map the whole time.
	A := AssociativeArray();
	for x in Domain(M) do
		N := M(x);
		if Type(N) eq Map then
			A[x] := MapToAssociativeArray(N);
		else
			A[x] := N;
		end if;
	end for;
	return A;
end function;

function H1(G, A, M)
	// Find all crossed morphisms modulo equivalence
	S := [g : g in Generators(G)];
	CM := [];
	PowerSet := Set(CartesianPower(A, #S));
	while #PowerSet gt 0 do
		for rho in [Representative(PowerSet)] do
			for a in A do
				E := < M[S[i]][a] * rho[i] * a^(-1) : i in [1..#S] >;
				Exclude(~PowerSet, E);	// Remove equivalent potential corssed morphisms
			end for;
			h := AssociativeArray();
			for i in [1..#S] do
				h[S[i]] := rho[i];
			end for;
			AddedNewOne := true;
			while #Keys(h) ne #G or AddedNewOne do
				AddedNewOne := false;
				for g1 in S, g2 in Keys(h) do
					if not(g2*g1) in Keys(h) then
						h[g2*g1] := M[g1][h[g2]] * h[g1];
						AddedNewOne := true;
					elif h[g2*g1] ne M[g1][h[g2]] * h[g1] then
						continue rho;	// Cocycle condition has not been satisfied.
					end if;
				end for;
			end while;
			Append(~CM, map<G->A | g:->h[g]>);
		end for;
	end while;
	return CM;
end function;

function HilbertNinety(nu, K, rho)
	B := 1.1;
	repeat
		repeat
			M0 := Matrix([[ &+[Random([-Floor(B)..Floor(B)])*K.1^e : e in [0..Degree(K)-1]] : i in [1..3]]: j in [1..3]]);
			M := &+[ ApplyGalois(M0, rho(g)) * nu(g) : g in Domain(nu) ];
			B +:= 0.1;
		until Determinant(M) ne 0;
	until {ApplyGalois(M, rho(g))^(-1)*M eq nu(g) : g in Domain(nu)} eq {true};
	return M;
end function;

function ParticularTwist(C, K, G, rho, nu: minimal:=true)
	// C is a curve over a Galois number field K
	// G is the (abstract) Galois group of K over Q
	// rho maps elements of G to automorphisms of K
	// nu is a cocycle from G to the group of automorphisms A of C

	// First some basic assertions, surely the method could be generalised
	assert(Type(C) eq CrvPln);
	assert(Genus(C) eq 3);

	// Apply Hilbert 90
	M := HilbertNinety(nu, K, rho)^(-1);
	R := CoordinateRing(Ambient(C));
	f := Evaluate(Equation(C), [&+[M[i][j]*R.j : j in [1..3]] : i in [1..3]]);
	D := ChangeRing(Curve(Ambient(C), f), Rationals());

	// Find curve
	if minimal then
		// this can be time consuming and also fail
		D := MinimizeReduce(D);
	end if;

	return D;
end function;

function AbsoluteAutomorphisms(C, A)
	K := BaseField(C);
	for i->M in A do
		b, lambda := IsPower(Determinant(M), 3);
		assert b; // Assert determinants are third powers.
		A[i] /:= lambda;
	end for;

	U := Roots(t^(3*#A) - 1, K) where t := PolynomialRing(Rationals()).1;
	O := EquationOrder(K);
	p := 1;
	while true do
		p := NextPrime(p);
		if p gt 10000 then
			assert(false);	// Failed to find good prime.
		end if;
		if p mod (3*#A) ne 1 or Discriminant(O) mod p eq 0 then
			continue;
		end if;
		Rtsp := Roots( DefiningPolynomial(O), GF(p) );
		if #Rtsp eq 0 then
			continue;
		end if;
		rho := hom<K->GF(p) | Rtsp[1][1] >;
		try
			Cp := BaseChange(C, rho);
			assert IsNonsingular(Cp);
			Ap := [ChangeRing(M, rho) : M in A];
		catch e
			print e;
			continue;
		end try;
		break;
	end while;

	Autp := [Automorphism(Cp, M) : M in Ap];
	Gp := AutomorphismGroup(Cp, Autp);
	_<X,Y> := FunctionField(Cp);
	Mp, nu, B := MatrixRepresentation(Gp);

	for i->M in A do
		PossMatrices := [u[1]*M : u in U];
		PossReductions := [ChangeRing(M, rho) : M in PossMatrices];
		j := Index(PossReductions, Transpose(nu(Autp[i]))^(-1));
		if j eq 0 then
			error "Could not find right scaling of automorphism matrix. Consider adding", 3*#A, "th roots of unity";
		end if;
		A[i] := PossMatrices[j];
	end for;

	assert {M1*M2 in A : M1, M2 in A} eq {true};

	return A;
end function;

intrinsic AllTwists(C::CrvPln, K::FldNum : CheckAutomorphisms:=true, AutGrp:=false, minimal:=false ) -> SeqEnum[CrvPln]
	{ compute all the twists of C over K }
	vprint Twists: Sprintf("AllTwists(C, K), where C:=%o, K:=%o", C, K);
	require Degree(K) gt 1 : "second argument cannot be the rationals";
	// First compute the Galois group of K to check that K is Galois.
	vprintf Twists: "Computing GaloisGroup(K)...";
	vtime Twists:
	G := GaloisGroup(K);
	require #G eq AbsoluteDegree(K): "K is not Galois";
	vprintf Twists: "Computing AutomorphismGroup(K)...";
	vtime Twists:
	G, _, rho := AutomorphismGroup(K);
	CK := ChangeRing(C, K);

	// Now compute the automorphisms of C_K and check that these are all geometric automorphisms.
	if AutGrp cmpeq false then
		vprintf Twists: "Computing automorphism of C over K...";
		vtime Twists:
		A := AutomorphismsOfPlaneQuartic(CK);
	end if;
	if CheckAutomorphisms then
		vprintf Twists: "Computing automorphism of C over Qbar...";
		vtime Twists:
		_, n := GeometricAutomorphismGroup(C);
		require #A eq n: "All automorphisms have to be defined over K.";
		vprint Twists : "Automorphism group checked";
	end if;
	// Lift automorphisms to GL3
	vprintf Twists: "Computing automorphisms in GL3...";
	vtime Twists:
	A := AbsoluteAutomorphisms(CK, A);

	// Find H1
	vprintf Twists: "Computing action on hom-set...";
	vtime Twists:
	M := map< G->Maps(A,A) | g:-> map<A->A | a:-> ApplyGalois(a, rho(g)) > >;
	vprintf Twists: "Caching action on hom-set...";
	vtime Twists:
	M := MapToAssociativeArray(M);
	vprint Twists : "Galois action on hom-set defined";
	vprintf Twists: "Computing H1...";
	vtime Twists:
	H1CK := H1(G, A, M);
	vprint Twists : "H1 found";

	// Find all twists
	L := [];
	for i->nu in H1CK do
		vprintf Twists : "Computing %o twist of %o...", i, #H1CK;
		vtime Twists:
		T := ParticularTwist(CK, K, G, rho, nu : minimal:=minimal);
		Append(~L, Curve(Ambient(C), DefiningEquation(T)));
	end for;
	vprint Twists : "AllTwists(C, K) done";
	return L, H1CK, A, G, rho;
end intrinsic;
