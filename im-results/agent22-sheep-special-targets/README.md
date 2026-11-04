# Complete source-shaped first-even predecessors of Sheep targets 3·2^a

**Agent22, 2026-11-04. Intermediate mathematical theorem with exact finite modular premises.** The following all-exponent classification is proved by elementary congruences and the source-matched Sheep first-even formulas. It has been tested independently by [certificate.py](certificate.py), but the universal statement has **not** yet been connected to authentic original Lean imports as a compiled theorem. This does not decide Sheep or BB(6).

## Theorem

For every natural a≥2, put Y=3·2^a. The **complete** set of genuine even first-return Sheep source states x satisfying E(x)=Y is

\[
\begin{aligned}
x_1(a)&=2\frac{3\cdot2^{a+1}-1}{5},
  &&\text{present exactly when }a\equiv0\pmod4,\\
x_2(a)&=4\frac{3\cdot2^{a+1}-3}{9},
  &&\text{present exactly when }a\text{ is odd},\\
x_3(a)&=8\frac{3\cdot2^{a+1}-5}{17},
  &&\text{present exactly when }a\equiv5\pmod8.
\end{aligned}
\]

These are distinct whenever multiple sources occur. Every displayed fraction is a positive odd generic cofactor of size at least five times its listed power of two and produces the exact source E transition. There are no other even E predecessors.

**Corollary (new complete infinite missing-incoming family):** For all natural k≥0 and all even source counters x, there is **no** first-even E edge
\[
E(x)=3\cdot 2^{4k+2}.
\]
The actual blank even-section start is 10, distinct from all these targets (the smallest is 12); therefore no actual blank E trajectory reaches any of them. This excludes **25% of the exceptional odd-part-three exponents**, but does not rule out all possible exceptional states, nor does it exclude additional halting powers 2^j.

## Complete all-a proof

Write an arbitrary legal even source as x=2^b v with b≥1 and odd v≥3.

**1. The intermediate odd-block length is zero.** The genuine E definition is E(x)=1+3^h u, where h≥0 and u odd. Since Y is divisible by three, h cannot be positive. Thus h=0 and the ordinary section transition F(x) must equal Y.

**2. Eliminate the entire exceptional source branch.** If v=3, the exact special section rule gives
\[
3\cdot2^a=3\cdot2^b+b+3.
\]
Reduction modulo three forces b≡0 (mod3), hence b≥3. The equation also forces a>b. It then implies
\[
b+3=3(2^a-2^b)\ge3\cdot2^b>b+3,
\]
a contradiction. The final strict inequality holds for every b≥3 by immediate induction.

**3. Bound every generic source valuation b.** If v≥5, F(x)=2^b v+b+(v−1)/2 and therefore
\[
(2^{b+1}+1)v=3\cdot2^{a+1}+1-2b.
\]
Writing M=2^(b+1)+1, the necessary congruence is
\[
3\cdot2^{a+1}\equiv2b-1\pmod M.
\]
For b≥5, the odd integer K=2b−1 satisfies 1<K<2^b; these inequalities persist by induction. Powers of two modulo M are of the form ±2^r for 0≤r≤b. **It is essential to retain the coefficient 3:** the necessary residues are ±3·2^r modulo M. For 1≤r≤b−1 we have 3·2^r<M, so both signed residues are even (the positive one is even, while M−3·2^r is odd; however its value is ≥M−3·2^(b−1)>2^(b−1), which exceeds K=2b−1 for b≥5). For r=0 the residues are 3 and M−3; neither is K for b≥5. For r=b the positive reduced residue is 2^b−1, the negative residue is 2^b+2; neither equals K because 2^b>2b for b≥5. Thus **every incoming generic source has b≤4**, without a finite-exponent or predecessor-depth cutoff. The ordinary single-power residue-gap lemma alone would not justify this step; the coefficient-three analysis above is required.

**4. Classify all four remaining valuations.** The congruence for b=1 has modulus five and period four, with the unique solution a≡0 mod4. For b=2 it has modulus nine, where reduction modulo three forces a odd, which is also sufficient. For b=3 it has modulus 17 and binary period eight, with unique solution a≡5 mod8. For b=4 the modulus is 33, and the left side is divisible by three whereas 2b−1=7 is not. These small modular periods are explicitly verified in the checker: 4,6,8,10 with allowed residues (0), (1,3,5), (5), and empty respectively.

**5. Verify sufficiency, parity and legality.** For each listed congruence the fraction defining v is an integer. Its numerator and odd denominator are odd, so v is odd. At the smallest allowed exponents (a=4,3,5 respectively) the values of v are 19,5,11. Every later permitted a in that class strictly increases v. Hence x=2^b v is a legal generic source. Substitution into the exact F equation gives F(x)=Y; Y−1 is odd, so the genuine first-even successor E(x) is exactly Y. Distinct valuations b give distinct sources.

This proves exhaustiveness and existence for every natural a≥2.

## Reproduction, scope, and next challenge

Run **python certificate.py** from this directory with Python 3.10+ standard library only. It independently reproduces all four small modular periods, checks high-b Fermat-gap inequalities through b=199 as an audit of the written induction, and directly enumerates exact legal even-section parents of 3·2^a for every 2≤a≤1000, matching the formulas with zero discrepancies.

The proof uses the source-authenticated F/E section formulas previously validated in [Agent16's Sheep even-return Lean archive](../agent16-sheep-even-return/README.md) and [Agent14's full inverse splitter](../agent14-sheep-even-inverse/SheepEvenSourceAlgebra.lean). A separately compiled **universal source-imported Lean theorem** for the new classification is still pending. Independent all-exponent review and external academic novelty checks are also pending.

A potentially valuable follow-up is to determine whether **any** odd-part-three state 3·2^a can occur on the genuine blank-start orbit. Its first 160,000 E returns contained none, and this theorem completely excludes a≡2 mod4. These finite observations give no proof for the other exponents.

## Formalization checkpoint, 2026-11-04

[SmallMods.lean](./SmallMods.lean) contains self-contained all-k Lean 4.36.0-rc2 kernel proofs of the four low source-valuation modular exclusions for the no-incoming target family `3*2^(4*k+2)`, together with a generic binary modular-period lemma. Local original toolchain compilation passed; all five declarations are audited with `#print axioms`. This certifies exactly the low-b modular arithmetic and leaves the high-b odd residue gap, the exceptional-source contradiction, and their original-source `SheepEven.EvenEdge` integration as **separate missing Lean proof obligations**. The pre-existing authentic E source was independently compiled in successful CI 41767327028. A further manual source-and-`SmallMods` [CI 41767978788](https://github.com/FlareZ123/bb6/actions/runs/41767978788) **succeeded**. It compiled the unchanged archived original Agent16 E semantics and the new source-independent Lean all-k low-b modular lemmas, with standard logical axioms only. It still does not prove the complete high-b and special-source exclusions in Lean.

[../agent22-sheep-new-cones/ConeCore.lean](../agent22-sheep-new-cones/ConeCore.lean) also supplies a generic Lean `no_reach_without_incoming` deduction from authentic E no-incoming premises, keeping those premises explicit.
