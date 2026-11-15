# Branch-10 q=0 boundary: finite inverse tree for (n,d)=(23,7)

**Status:** exact arithmetic derivation; the imported Lean proof has not yet been written. This is a proposed closure of the q=0 branch left by the depth-14 affine certificate. It uses only existing pair-level root lemmas and must be checked/compiled in the repository.

## Affine seed and q=0 values

For branch 10, c=6 and C=21. At n=23,d=7:
- A = 64*2^23+32 = 536870944
- B = 64*(2^24-1) = 1073741760
- a = 2^23*(7+6)+(2*7-3*23-21)/4 = 109051885
- b = 2*(a-7)+1 = 218103757

At q=0 the affine family evaluates to the pair (a,b). The affine F/S/E transformations preserve these q=0 values by the corresponding pair-level inverse maps.

The first inverse step is forced F because b mod4=1:
(109051885,218103757) ->F (54525941,327155642).

At the latter pair b mod4=2, so odd_back permits F or S:
- F gives (27262969,381681583), with (a mod8,b mod4)=(1,3), forbidden by reach_allowed/Allowed.
- S gives (136314845,163577823).

Three forced F steps from this S child give:
(136314845,163577823)
 ->F (68157421,299892668)
 ->F (34078709,368050089)
 ->F (17039353,402128798).

Call the final pair P=(17039353,402128798). This is exactly where the affine coefficient A becomes odd and the affine certificate stops.

## Direct inverse tree from P

The pair-level lemmas used below are:
- BB429NewResidue.odd_back and even_back;
- BB429NewResidue.reach_allowed;
- BB429LowOddMod8.rooted_even_parity: positive even first coordinate forces second coordinate mod4=2;
- BB429Extra11.blank_not_11_1: a blank-reachable pair with first coordinate mod16=11 must have second coordinate mod4!=1.

If P were blank-reachable, odd_back gives F or S (P has odd first coordinate >=13 and second mod4=2).

**S(P)** is:
(117571546,201064401),
whose first coordinate is positive even and whose second coordinate is 1 mod4. This contradicts rooted_even_parity.

**F(P)** is:
(8519675,419168151).
Its second coordinate is 3 mod4, so odd_back allows only F, giving:
(4259836,427687826).
This has positive even first coordinate and second mod4=2, so even_back gives the unique E predecessor:
(111181789,213843913).
This is odd with second mod4=1, so odd_back allows only F:
(55590893,325025702).
Here the second coordinate is 2 mod4, so odd_back gives F or S:
- S gives (136847312,162512853), positive even with second mod4=1, contradicting rooted_even_parity.
- F gives (27795445,380616595), odd with second mod4=3, so only F:
(13897721,408412040),
odd with second mod4=0, so only F:
(6948859,422309761).
The final pair has first coordinate mod16=11 and second coordinate mod4=1, contradicting blank_not_11_1.

Thus both alternatives at every odd split are excluded, and the even step is unique. Therefore P is not blank-reachable. Back-propagating through the initial F and the two F/S alternatives proves the q=0 seed (109051885,218103757) is not blank-reachable.

## Proof obligations for Lean integration

The proof must preserve the disjunction in odd_back: at every node with second mod4=2, both F and S children must be ruled out. At nodes with second mod4!=2, the S alternative is impossible from odd_back's explicit mod4=2 premise, leaving only F. The even_back theorem is a unique predecessor statement. The arithmetic identities above can be discharged by omega after substituting the concrete numerals.

No claim is made here about the q>0 branches; the note only addresses the q=0 boundary for this one residue class.
