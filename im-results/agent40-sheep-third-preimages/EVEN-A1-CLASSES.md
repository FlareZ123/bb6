# Sixteen further even-exponent Sheep halting-target exclusions

**Agent 40, 2026-11-02. Intermediate theorem, not a BB(6) solution.** The proof is an all-exponent arithmetic argument about the established Sheep return map. Standalone Lean 4.36.0-rc2 files certify the fixed-modulus parts, and exact inverse simulation tests the resulting formulas. The machine-to-map bridge comes from Google DeepMind's published formalization, not this local standalone module.

## Statement and consequence

Machine `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Published return map from the actual blank-reachable section starts at t=5. Write t=2^a u, u odd:

`F(t)=undefined` when u=1; `F(t)=t+a+3` when u=3; `F(t)=t+a+(u−1)/2` when u≥5.

**Theorem.** Let j≥22 satisfy
`j mod 180 ∈ R={2,22,26,38,58,62,70,98,106,110,130,142,146,166,170,178}`.
Set `p=(2^(j+1)+1)/3`, `x=(2^(j+3)−2)/15`. These are integers greater than five. The **complete inverse fibers** among all t≥3 are

`F⁻¹(2^j)={p}`, `F⁻¹(p)={x}`, `F⁻¹(x)=∅`.

Thus the actual orbit from t=5 never visits 2^j for any such j. The only exponent in the listed classes below 22 is j=2, whose target 4 is already smaller than the start 5. Every defined F(t) increases t, so 4 is unreachable too. Consequently *all* exponents in these sixteen infinite residue classes are excluded, including j=2.

These classes have density 16/180=4/45 among nonnegative halting-target indices. They are all j≡2(mod4) and disjoint from earlier Agent15/16 excluded classes (even classes j≡0mod4, plus j≡1mod4 and odd j≡3mod4 classes) and this Agent's earlier even j≡0mod4 and odd classes. With the prior 157/360, additional 5/216 and 7/300, the new **combined excluded exponent-index density** is

`157/360+5/216+7/300+16/180 = 1543/2700 ≈57.148148%`.

This does **not** prove the Sheep Machine never halts or determine BB(6).

## Universal algebra and the exceptional branch

For the generic u≥5 branch, the exact identity is

`2F(2^a u)=(2^(a+1)+1)u+2a−1.` (G)

**Uniform residue-gap lemma:** with M=2^(a+1)+1, every power 2^e modulo M equals either 2^r or M−2^r for some 0≤r≤a, because `2^(a+1)≡−1 (mod M)`. The positive representatives are 1 or even, while the latter representatives are ≥2^a+1. Thus for *every* a and e, `2^e mod M` cannot equal an odd D satisfying 1<D<2^a.

The exceptional u=3 images are `f(a)=3·2^a+a+3`, strictly increasing in a. They are never powers of two: f(0)=6, f(1)=10, f(2)=17; for a≥3, `2^(a+1)<f(a)<2^(a+2)`. Nor do they equal p or x for j≥22: one has

`f(j−3)<p,x<3·2^(j−2)<f(j−2)`.

Indeed `p−f(j−3)=(7/24)2^j+1/3−j` and `x−f(j−3)=(19/120)2^j−2/15−j`. Both differences are positive at j=22 and remain positive by induction, because the exponential contribution doubles while j increases only by one. The upper inequalities are immediate from p≈(2/3)2^j and x≈(8/15)2^j, both smaller than (3/4)2^j for j≥22. Therefore no exceptional branch provides a predecessor to any of the three targets, and u=1 halts without an image.

The residue classes R imply j≡2(mod4), j mod12∈{2,10}, and j mod6∈{2,4}. The following six uniform modular gate inequalities are **Lean-kernel checked for every j∈R**, by reducing each exponent to a fixed base residue modulo its full period (all dividing 180):

`2^(j+4)%9≠7`, `2^(j+4)%25≠19`, `2^(j+4)%27≠22`,
`2^(j+4)%13≠9`, `2^(j+2)%27≠7`, `2^(j+2)%9≠4`.

The certificates are in `EvenA1ResidueCert.lean`, where `smallGates_all` has no sorryAx.

## Exact first inverse fiber

Solving F(2^a u)=2^j on u≥5 in (G) yields

`2^(j+1)=(2^(a+1)+1)u+2a−1.` (1)

If a≥2, D=2a−1 is odd and 1<D<2^a (base a=2, then induction). Reduction modulo M contradicts the residue gap. If a=1, equation (1) demands `2^(j+1)≡1(mod5)`, whereas j≡2(mod4) makes that residue 3. If a=0, the only solution is u=p, an odd integer ≥5 for even j≥22. Direct substitution proves F(p)=2^j. Hence `F⁻¹(2^j)={p}`.

## Exact second inverse fiber

Solving F(2^a u)=p in (G), after multiplying by three, yields

`2^(j+2)+5−6a=3(2^(a+1)+1)u.` (2)

For a≥5, D=6a−5 is odd in (1,2^a), by the base 25<32 at a=5 and induction. The gap lemma excludes all these valuations. The remaining a≤4 cases are:

| a | required modular value | contradiction |
|---:|---|---|
| 0 | `2^(j+2)≡4(mod9)` | modular gate above |
| 1 | possible | exact source is x |
| 2 | `2^(j+2)≡7(mod27)` | modular gate above |
| 3 | `2^(j+2)≡13(mod17)` | j+2 multiple of four; 2^(4n) modulo17 is 1 or 16 |
| 4 | `2^(j+2)≡8(mod11)` | even powers modulo11 are {1,3,4,5,9} |

At a=1, equation (2) uniquely yields `u=(2^(j+2)−1)/15`. Since j is even and ≡2(mod4), the numerator is divisible by both 3 and 5; the quotient is odd and ≥5. The source is 2u=x, and direct substitution yields F(x)=p. Hence `F⁻¹(p)={x}`.

## Exact third inverse fiber

Solving F(2^a u)=x in (G), multiply by fifteen:

`2^(j+4)+11−30a=15(2^(a+1)+1)u.` (3)

Therefore every predecessor valuation must satisfy
`2^(j+4) ≡ 30a−11 (mod 15(2^(a+1)+1))`.

For a≥8, D=30a−11 is odd and in (1,2^a), starting with 229<256 at a=8 and preserved since doubling 2^a outpaces the 30-unit increase. The residue-gap lemma excludes all a≥8. For 0≤a≤7:

| a | D=30a−11 | necessary modulus | contradiction |
|---:|---:|---:|---|
| 0 | −11 | 9 | `2^(j+4)%9 ≠7` |
| 1 | 19 | 25 | `2^(j+4)%25 ≠19` |
| 2 | 49 | 27 | `2^(j+4)%27 ≠22` |
| 3 | 79 | 17 | 79≡11; no power of two is 11 modulo17 |
| 4 | 109 | 11 | 109≡10; j+4 even; no even power of two is 10 modulo11 |
| 5 | 139 | 13 | 139≡9; j+4 modulo12 is 2 or 6, giving residues 4 or 12, never 9 |
| 6 | 169 | 43 | 169≡40; no power of two is 40 modulo43 |
| 7 | 199 | 257 | 2^8≡−1 modulo257, residues ±2^r for 0≤r≤7, none 199 |

All the unbounded-power congruences are proven by `smallGates_all`, `allPow17Not11`, `evenPower11Not10`, `allPow43Not40`, `allPow257Not199` in `EvenA1ResidueCert.lean`. The second-level modulo11 and 17 exclusions are proved there as `evenPower11Not8` and `fourPower17Not13`. Lean 4.36.0-rc2 reports only standard axioms propext and Quot.sound for all printed theorems, **no sorryAx**. This exhausts all possible valuations in equation (3), and the u=3 and u=1 branches were excluded above. Therefore `F⁻¹(x)=∅`.

Since x>5 and cannot have an incoming F-edge, it is unreachable from the actual section start 5; its child p and grandchild 2^j are likewise unreachable. For the small outlier j=2, the target 4<5 and every defined F-value increases. This proves all claimed exclusions.

## Reproduction and open issue

`EvenA1ResidueCert.lean` is standalone and **does not** yet formalize the global inverse theorem or import the certified original TM map; the residue-gap and exceptional-branch inequalities are complete handwritten proofs above. `verify_even_a1.py` verifies complete inverse fibers at all three depths for **176 matching exponents through j=2000** and **4,000 independent modular instances**. Both tests passed locally. Published map sources and earlier inverse results are linked in the directory's `README.md`, `ODD-CLASSES.md`, and `im-results/agent14-sheep-preimages/` through `agent16-sheep-power-preimages/`.

**The missing BB(6) step remains deciding whether the actual trajectory from t=5 ever reaches *any* surviving power of two.** This result rules out more infinite target families but does not decide the holdout.
