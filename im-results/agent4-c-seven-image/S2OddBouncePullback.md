# A third strict-image candidate from the s2 odd-bounce sector

## Status

This is a new, explicit candidate source exclusion for a thin subfamily of the second affine strict sixth/seventh image family. The parameter pullback is an exact arithmetic derivation. The source-root argument below is a detailed proof skeleton assembled from existing source theorems, but it has not yet been formalized as a new Lean theorem or run through CI. Do not count this as an established third exclusion until the parent enumeration and normalizer chain are formalized and checked.

## Image-family coordinates

Use the existing affine image family

**V(u,v) = (641+1024u, 574+1024v).**

The H1 branch of its established three-parent decomposition has two parents P0 and P2; P2 has unique parent

**R(u,v) = (471+276u+548v, 644+374u+750v).**

The direct affine parent of R is

**P(u,v) = (1113+650u+1298v, 321+187u+375v).**

Consider the subfamily

**v+93u = 42 (mod 128).** (S2)

This implies u+v = 2 (mod 4). Equivalently, put u+v=2+4t; then (S2) is exactly

**v = 28+11t (mod 32).**

Indeed, multiplying the latter congruence by four and using 4t=u+v-2 gives 7v=38-11u (mod 128); the inverse of 7 modulo 128 is 55, giving v+93u=42 (mod 128).

## Exact two-parent structure of R

Let

**T = 558+325u+649v.**

Then R.x+R.y+1=2T. Under (S2), write u+v=2+4t. Substituting u=2+4t-v gives

**T = 1208+1300t+324v.**

Since v=28+11t (mod 32), we have t+v=0 (mod 4), hence

**T = 8 (mod 16).**

Therefore R.x+R.y+1 has 2-adic valuation exactly 4.

The complete section-preimage grammar then gives exactly two parents of R:

1. The direct affine parent P(u,v).
2. The odd-bounce parent

**Q(u,v) = (601+650t+162v, 1598+1723t+431v).**

Reason: R.x+R.y is odd, so the even-a bounce branch is impossible. The a=0 branch is impossible for the same parity reason; the exceptional a=1 branch is impossible because R.x+R.y+1 has valuation exactly 4 and is far larger than 16. In the a odd bounce branch, the second equation forces the bounce exponent n to be odd. Since a+3 is even and v2(R.x+R.y+1)=4, n≤2, hence n=1. Solving the two source equations gives Q above. The remaining 2k≤a branch is exactly P.

This exact parent enumeration should be formalized from section_preimage_all_iff; it is not yet a committed Lean theorem.

## Q is blank-root unreachable

For Q above,

- Q.x+Q.y = 2199+2373t+593v = 3 (mod 8);
- Q.y = 1598+1723t+431v = 2 (mod 16);
- Q.y≥34.

The first two congruences follow directly from v=28+11t (mod 32). Thus Q lies in the second Agent34 three-edge cone, and the existing cone_blank_unreachable theorem gives all-time blank-root nonreachability of Q.

## P is blank-root unreachable by the full forced normalizer

P is odd/odd. Its sum is

**P.x+P.y = 3108+3348t+836v.**

It is 0 modulo 4 and is either 4 or 12 modulo 16 under v=28+11t (mod 32), so the oddLowGate applies. Its exact oddLow parent is

**A = 1552+1674t+418v,**
**B = 1122+1211t+303v.**

Under the same congruence,

- A = 8 (mod 16);
- B = 6 (mod 32).

In particular B+2 is divisible by 8. Put **W=(B+2)/8**. The stronger modulus 32 gives W=1 (mod 4), and W≥141.

The full forced normalizer uses the six-residue even-right affine parent F(x,y)=(x+y-2,(y-2)/2). Starting from (A,B), the first three states are exactly

- F0 = (A,B);
- F1 = (A+8W-4, 4W-2);
- F2 = (A+12W-8, 2W-2);
- F3 = (A+14W-12, W-2).

At F0, F1, F2, the right coordinate is even and at least 6, and the coordinate sum is respectively 6, 6, and 4 modulo 8. Thus sixEvenRightGate applies at each of these three states. The competing oddLow, evenSeven, and evenAffine gates are false there.

At F3, the first coordinate is even, the second is odd, and

**F3.x+F3.y = 1 (mod 4).**

Consequently none of the four normalizer gates applies at F3: oddLow is false by first-coordinate parity; evenSeven is false because (F3.x+F3.y+1) is 2 modulo 4, not 0; both even-right gates are false by second-coordinate parity. Hence fullForcedNormalize(A,B)=F3.

The exact theorem blank_reach_iff_fullForcedNormalize reduces blank reachability of (A,B) to that of F3. The existing blank_no_odd_sum_one obstruction excludes F3, since F3.y=W-2 is odd and at least 5 and its coordinate sum is 1 modulo 4. Therefore (A,B) is blank-root unreachable. By oddodd_lowval_blank_reach_iff, P is blank-root unreachable.

Since both exact parents P and Q of R are blank-root unreachable, R is blank-root unreachable.

## Consequence for V

The established three-parent classification of V gives D, H1, H3 as its only immediate parents.

- H3 is itself in the Agent34 cone (sum 3 modulo 8, right coordinate 2 modulo 16), so it is blank-root unreachable.
- H1 has parents P0 and P2. P0 has odd right coordinate and coordinate sum 1 modulo 4, so the odd-image obstruction excludes it. P2 has unique parent R, which was excluded above. Hence H1 is blank-root unreachable.
- D has no six-step incoming chain by the existing no_six_D theorem. The first six blank-root states can be checked directly, and D is far outside that finite list, so D is blank-root unreachable.

Thus V(u,v) is blank-root unreachable for every (u,v) satisfying (S2), provided the indicated existing parent and normalizer lemmas are composed as described.

This is a source-root exclusion, not yet an exact six/seven incoming-depth theorem.

## Exact high-stop pullback

Let

**K(j,m)=2^(2m+2)(j+3)-(j+3m+5).**

The high-stop equation is k+j+3m+5=2^(2m+2)(j+3). For image membership, j=319+512u and k=574+1024v.

The exact pullback of (S2) is

**j = 319 (mod 512),**
**3m+102921 = 185j (mod 131072).** (S2-pullback)

Forward direction: the same small-m residue check used for the other strict families forces m≥7; reducing the stop equation modulo 512 then gives m=42 (mod 512), hence m≥42 and 131072 divides 2^(2m+2). From v+93u=42 (mod 128),

k+95232u = 43582 (mod 131072), since k=574+1024v and v+93u=42 (mod 128).

Substitute j=319+512u into the stop equation modulo 131072 to obtain 3m+102921=185j.

Conversely, suppose the two congruences in (S2-pullback) hold. Reducing the second modulo 512 gives m=42 (mod 512), so 131072 divides the power term. The stop equation then gives

k+j+3m+5 = 0 (mod 131072), and therefore k+95232u = 43582 (mod 131072),

where u=(j-319)/512. Therefore k=574 (mod 1024), so k=574+1024v for a natural v, and the stronger congruence gives v+93u=42 (mod 128). This recovers (S2).

For each j-class modulo 512, the second congruence fixes one m-class modulo 131072 because 3 is invertible modulo 131072. Thus the exact parameter-lattice density is

**1/(512*131072) = 1/2^26.**

Writing j=319+512u, the same class can be written explicitly as

**m = 72746+75264u (mod 131072).**

This is an immediate inverse of 3 modulo 131072 applied to the linear congruence above, and it visibly reduces to m=42 (mod 512).

The family is disjoint from the older diagonal (u+v=0 mod 4) and the previous s3 cylinder (u+v=3 mod 4), since (S2) forces u+v=2 mod 4.

If the source-root composition is formalized, the combined three-family exclusion density becomes 41/2^26, leaving 215 of the 256 m-classes modulo 131072 in the common j=319,m=42 modulo 512 base cylinder outside these three exclusions.

## Formalization work still required

1. Prove the exact two-parent classification of R from section_preimage_all_iff under (S2).
2. Formalize the three sixEvenRightGate reductions of (A,B), including the terminal fullForcedNormalize value F3.
3. Compose the Agent34 cone exclusion for Q, the Agent3 full-normalizer/odd-image exclusion for P, and the established D/H1/H3 parent classification to prove V blank-root unreachable.
4. Prove the parameter-only pullback equivalence in Lean and add the resulting exclusion to the C58 and SixAll high predicates.
5. Run a fresh original-source CI audit before treating this as an established exclusion.

No claim is made here that this new cylinder is already excluded by the current Lean source theorem or that it decides Machine C or BB(6).
