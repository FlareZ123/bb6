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

Reason: R.x+R.y is odd, so the even-a bounce branch is impossible. The a=0 branch is impossible for the same parity reason; the exceptional a=1 branch is impossible because R.x+R.y+1 has valuation exactly 4 and is far larger than 16. The a≥2, k=0 branch would force R.y=2, also impossible since R.y≥644. In the a odd bounce branch, the special y=3 alternative is impossible because R.y≥644. In the remaining y≥5 branch, the second equation forces the bounce exponent n to be odd. Since a+3 is even and v2(R.x+R.y+1)=4, n≤2, hence n=1. Solving the two source equations gives Q above. The remaining 2k≤a branch is exactly P.

This exact parent enumeration should be formalized from section_preimage_all_iff; it is not yet a committed Lean theorem.

## Q is blank-root unreachable

For Q above,

- Q.x+Q.y = 2199+2373t+593v = 3 (mod 8);
- Q.y = 1598+1723t+431v = 2 (mod 16);
- Q.y≥34.

The first two congruences follow directly from v=28+11t (mod 32). Thus Q lies in the second Agent34 three-edge cone, and the existing cone_blank_unreachable theorem gives all-time blank-root nonreachability of Q.

## P is blank-root unreachable by the six-right normalizer

P is odd/odd. Its sum is

**P.x+P.y = 3108+3348t+836v.**

It is 0 modulo 4 and is either 4 or 12 modulo 16 under v=28+11t (mod 32), so the oddLowGate applies. Its exact oddLow parent is

**A = 1552+1674t+418v,**
**B = 1122+1211t+303v.**

Under the same congruence,

- A = 8 (mod 16);
- B = 6 (mod 32).

In particular B+2 is divisible by 8. Put **W=(B+2)/8**. The stronger modulus 32 gives W=1 (mod 4), and W≥141.

Use the dedicated source-exact six-right normalizer from Agent46, with parent F(x,y)=(x+y-2,(y-2)/2). Starting from (A,B), its first three states are exactly

- F0 = (A,B);
- F1 = (A+8W-4, 4W-2);
- F2 = (A+12W-8, 2W-2);
- F3 = (A+14W-12, W-2).

At F0, F1, F2, the right coordinate is even and at least 6, and the coordinate sum is respectively 6, 6, and 4 modulo 8. Thus sixEvenRightGate applies at each of these three states. At F3 the right coordinate W-2 is odd, so the six-right normalizer stops. Moreover

**F3.x+F3.y = 1 (mod 4).**

The exact theorem blank_reach_iff_sixEvenRightNormalize reduces blank reachability of (A,B) to that of F3. Equivalently, sixEvenRightExcluded(A,B)=true, and the existing sixEvenRightExcluded_sound theorem excludes blank reachability. Therefore (A,B) is blank-root unreachable. By oddodd_lowval_blank_reach_iff, P is blank-root unreachable.

Since both exact parents P and Q of R are blank-root unreachable, R is blank-root unreachable.

## Consequence for V

The established three-parent classification of V gives D, H1, H3 as its only immediate parents.

- H3 is itself in the Agent34 cone (sum 3 modulo 8, right coordinate 2 modulo 16), so it is blank-root unreachable.
- H1 has parents P0 and P2. P0 has odd right coordinate and coordinate sum 1 modulo 4, so the odd-image obstruction excludes it. P2 has unique parent R, which was excluded above. Hence H1 is blank-root unreachable.
- D has no six-step incoming chain by the existing private no_six_D theorem in CSixSeventhStrict. Expose it or add a public wrapper. The blank-root states at times 0 through 5 are (5,1), (3,4), (4,7), (20,4), (12,10), (17,11); meanwhile D.x≥1213 and D.y≥286. Thus D is also blank-root unreachable.

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

## Complementary q-even lift (partially resolved)

The other lift of the same Q-cone congruence is (v=12+11t\pmod{32}), still under (u+v=2+4t) with (u,v\in\mathbb N). The natural-number parameterization must therefore be
\[
v=12+11t-32z,\qquad u=32z-7t-10,
\]
with
\[
7t+10\le 32z\le 12+11t.
\]
The earlier plus-sign expression (v=12+11t+32z) is incompatible with (u+v=2+4t) for nonnegative (u,z); the formulas in this section are corrected accordingly.

For this lift, the first odd/odd parent and its two-step six-even-right normalizer are
\[
A=6568+6272t-13376z,\qquad
W=(B+2)/8=595+568t-1212z,
\]
\[
F_2=(A+12W-8,2W-2)
=(13700+13088t-27920z,\;1188+1136t-2424z),
\]
with
\[
F_{2,x}+F_{2,y}=8S,\qquad S=1861+1778t-3793z.
\]

A source-exact subfamily is now closed:
\[
2t-z\equiv1\pmod8.
\]
This implies (z) is odd and (S\equiv6\pmod8), so (S\equiv2\pmod4). The complete even-even sum-zero parent theorem then leaves exactly two possible source parents of (F_2):

- Direct parent
  \[
  D=(14886+14224t-30344z,\;593+568t-1212z).
  \]
  Since (z) is odd, (D) lies in the exact even-left/odd-right valuation-two sector ((D_x+D_y+1)\equiv4\pmod8). Its unique source parent is
  \[
  U=(7737+7396t-15778z,\;4164+3982t-8495z),
  \]
  which has odd right coordinate and coordinate sum (2\pmod4). This contradicts the source-certified odd-right image invariant, whose only possible sum residues are (0,3\pmod4).

- Bounce parent
  \[
  E=(3720+3556t-7586z,\;6173+5902t-12591z).
  \]
  It is even-even with sum (2\pmod4), so its unique source parent is the six-even-right affine parent
  \[
  H=(E_x+E_y-2,\;(E_y-2)/2).
  \]
  Under (2t-z\equiv1\pmod8), (H_y) is odd and (H_x+H_y\equiv1\pmod4), again forbidden by the source odd-right image invariant.

Thus (F_2) is blank-unreachable for every natural (t,z) satisfying the upper bound (32z\le12+11t) and (2t-z\equiv1\pmod8). The formal proof is in [S2QEvenResidue.lean](S2QEvenResidue.lean), currently awaiting its fresh Lean CI audit.

This is a genuine partial closure of the complementary lift's normalizer residual, not yet a full blank-root exclusion for the original image state (V=(641+1024u,574+1024v)). The remaining composition through the P/R/V parent tree and the high-stop parameter pullback are still open.

A concrete infinite valid slice is
\[
t=32n+2,\qquad z=8n+3,\qquad n\ge1,
\]
which gives
\[
u=32n+72,\qquad v=96n-62.
\]
It satisfies the naturality bounds and the congruence above.

## Concrete arithmetic test vector

The small instance u=4, v=54 satisfies v+93u=42 (mod 128), with t=14. It gives

- R=(31167,42640);
- P=(73805,21319);
- Q=(18449,48994), with Q.x+Q.y=3 (mod 8) and Q.y=2 (mod 16);
- A=47560, B=34438, W=4305;
- F1=(81996,17218), F2=(99212,8608), F3=(107818,4303), with F3.y odd and F3.x+F3.y=1 (mod 4);
- j=2367 and m=111658 (mod 131072), which satisfy 3m+102921=185j exactly in this representative. The high-stop value K(j,m) is 55870 (mod 131072), i.e. 574+1024*54 (mod 131072), so the induced image parameter is v=54 (mod 128), not necessarily the minimal representative v=54.

This is a useful concrete test vector for the eventual Lean parent-enumeration and normalizer proofs; it is not a substitute for them.
A deterministic residue sweep over u=0,...,99, taking the least nonnegative v with v+93u=42 (mod 128), also checked t-integrality, W=1 (mod 4), the Q cone residues, the F3 odd/sum-one residues, and the pulled-back m congruence for all 100 representatives. Reproduce it with `python3 check_s2_residues.py` in this directory. This is only an arithmetic sanity check, not a proof.

## Formalization work still required

1. Prove the exact two-parent classification of R from section_preimage_all_iff under (S2).
2. Formalize the three sixEvenRightGate reductions of (A,B), including sixEvenRightNormalize(A,B)=F3 and the sixEvenRightExcluded_sound application.
3. Compose the Agent34 cone exclusion for Q, the Agent46 six-right-normalizer plus odd-image exclusion for P, and the established D/H1/H3 parent classification to prove V blank-root unreachable; expose or wrap the currently private no_six_D lemma.
4. Prove the parameter-only pullback equivalence in Lean and add the resulting exclusion to the C58 and SixAll high predicates.
5. Run a fresh original-source CI audit before treating this as an established exclusion.

No claim is made here that this new cylinder is already excluded by the current Lean source theorem or that it decides Machine C or BB(6).
