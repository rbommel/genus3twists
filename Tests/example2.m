AttachSpec("spec");
SetVerbose("Twists", 1);

_<t> := PolynomialRing(Rationals());
K := CyclotomicField(288);

P2<x,y,z> := ProjectivePlane(Rationals());
f := x^4 + y^4 + z^4;
C := Curve(P2, f);

T := AllTwists(C, K);

print {* exists { p : p in PrimesInInterval(1100, 1200) | not(IsIsomorphicPlaneQuartics(ChangeRing(T[i], GF(p)), ChangeRing(T[j], GF(p)))) } : j in [1..#T] | i ne j *} where i := Random(1,#T);	// Sanity check: check that random twist is non-isomorphic to each other twist.
