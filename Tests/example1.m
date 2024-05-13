AttachSpec("spec");
AttachSpec("~/CHIMP/CHIMP.spec");
SetVerbose("Twists", 1);

_<t> := PolynomialRing(Rationals());
K := NumberField(t^3 - t^2 - 437236009777629974*t + 111279775306753741061459296);
_<X> := PolynomialRing(K);
K1<a> := ext< K | X^3 - X^2 - 10*X + 8 >;
L := AbsoluteField(K1);
L := Polredabs(L);

P2<x,y,z> := ProjectivePlane(Rationals());
f := -286738375*x^4 - 2493795*x^3*y - 4763677*x^3*z + 770678*x^2*y^2 - 416924*x^2*y*z + 770678*x^2*z^2 - 4763677*x*y^3 - 416924*x*y^2*z - 416924*x*y*z^2 - 2493795*x*z^3 - 286738375*y^4 - 2493795*y^3*z + 770678*y^2*z^2 - 4763677*y*z^3 - 286738375*z^4;
C := Curve(P2, f);

T := AllTwists(C, L);

print {* exists { p : p in PrimesInInterval(1100, 1200) | not(IsIsomorphicPlaneQuartics(ChangeRing(T[i], GF(p)), ChangeRing(T[j], GF(p)))) } : i,j in [1..#T] | i lt j *};	// Sanity check: check that each pair of twists is non-isomorphic modulo some prime p.
