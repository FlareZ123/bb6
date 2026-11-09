# Machine C: four new high-stop lattices from sharp two-versus-three ancestry sectors

**Agent 4, 9 November 2026.** Original six-state two-symbol Machine C transition table: 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC. The source first-return map is BB6.Agent46.secNext, starting at section (5,1). The results use genuine original source edges, all times, and no cutoff.

## Main theorem

For every nonnegative s,t of the same parity, set
\[
T_{s,t}=(8s+1,16t+20).
\]
There are exactly two consecutive **incoming** original section edges and no three-edge incoming chain into this target. The unique predecessors are
\[
P_{s,t}=(8s+16t+19,8t+9),\qquad
Q_{s,t}=(4s+12t+12,2s+10t+9).
\]
Both Q->P and P->T are genuine source edges. The source-exact inverse grammar BB6.Agent46.section_preimage_all_iff forces these parents, including arbitrary bounce depths and all exceptional cases. But Q has odd second coordinate at least 9 and sum \(6s+22t+21\equiv1\pmod4\), violating the original-source odd-second image theorem. Thus a third incoming edge is impossible. The genuine blank section starts (5,1)->(3,4)->(4,7), so it avoids this sector at every return time.

The parity condition is the union of two disjoint residue cylinders:
\[
(x\bmod16,y\bmod32)=(9,4)\quad(y\ge36),\qquad
(x\bmod16,y\bmod32)=(1,20)\quad(y\ge20).
\]
These occupy two of 512 residue cells, asymptotic density \(1/256\) in section-coordinate space. This is a **sharp** \(I_2\setminus I_3\) sector. Its sum \(x+y\equiv5\pmod8\) distinguishes it from the Agent34 preexisting strict-three-depth cones at sums 1 or 3 modulo 8.

## True high-stopping pullback

For a high-family potential halting target (2j+3,k), the exact stopping equation is
\[
k+j+3m+5=2^{2m+2}(j+3).
\]
The source-connected theorems high_stop_blank_unreachable and high_stop_blank_unreachable_b exclude each of the following infinite disjoint parameter lattices for all \(m\ge4\), all \(j\), and all blank section times:
\[
\begin{aligned}
&j\bmod8=3,\quad (j+3m)\bmod32=23,\\
&j\bmod8=7,\quad (j+3m)\bmod32=7.
\end{aligned}
\]
The combined theorem high_stop_two_lattices excludes their union. Each lattice has natural density \(1/256\) of parameter pairs; combined density is \(1/128\). Explicit infinite first line: \(j=3,m=28+32r\). The second includes \(j=7,m=32+32r\).

These are unconditional original-blank section nonreachability results. They do not decide Machine C's complete halting behavior or the exact value of BB(6). A local transcription scan of the prior highAllowedValSixFull combined filter over j=0..255, m=16..271 left all 512 new lattice points eligible; this finite observation does not replace a quantified old-sieve admission proof.

## Formal source and verification

- [CThreeArithmetic.lean](CThreeArithmetic.lean): all-parent uniqueness for source-exact inverse grammar.
- [CThreeSource.lean](CThreeSource.lean): first cylinder, arbitrary-start no-three-edges and blank-root exclusion.
- [CThreeStop.lean](CThreeStop.lean): first high-stop lattice and explicit infinite family.
- [CThreeGenericSource.lean](CThreeGenericSource.lean): parity-diagonal strip, blank-root exclusion, second cylinder.
- [CThreeGenericStop.lean](CThreeGenericStop.lean): second high-stop lattice and combined theorem.
- [CThreeWit.lean](CThreeWit.lean): real incoming one/two edge witnesses and sharp exact-depth theorem.

Original-source Lean 4.36.0-rc2 CI: [first lattice 42573651217](https://github.com/FlareZ123/bb6/actions/runs/42573651217) (SUCCESS) and [double lattice 42574588451](https://github.com/FlareZ123/bb6/actions/runs/42574588451) (SUCCESS). The exact two-edge witness and strict two-versus-three source theorem also passed [original-source CI 42574936825](https://github.com/FlareZ123/bb6/actions/runs/42574936825) (SUCCESS); see the [manual source workflow](../../.github/workflows/agent4-c-three-ancestry.yml). All new theorems report only standard Lean logical axioms, with no sorryAx.

Relationship to other research: Agent45's [three-step image classification](../agent45-c-three-step/README.md) is broader and may imply this particular non-I3 cylinder. The explicit original-source kernel-certified sharp sector and its two all-time high-stop pullbacks are the present deliverables. BB(6) remains open.

## Prior-work boundary (9 November follow-up)

The general even-right, sum-one inverse uniqueness lemma `only_direct_mod4_one` was added as an explicit self-contained arithmetic bridge, **not an independently new theorem**: Agent15 previously proved the stronger `section_sum_one_even_iff_affine` and `section_even_right_iff_affine` (`im-results/agent15-c-even-source/EvenRightUnique.lean`), while Agent3 had already certified the sharp I1-not-I2 cylinder `(x%4=1,y%8=0,y>=16)` in `MixedEvenEightSharp.lean`. That older sector is disjoint from our sharp I2-not-I3 targets, which have right coordinate 4 modulo 8. No novelty is claimed for the general uniqueness lemma or the older one-step sector. The new source-certified contribution is the different exact two-step sector and the specific high-stopping pullbacks. The refactored source arithmetic was successfully verified by [CI 42576141381](https://github.com/FlareZ123/bb6/actions/runs/42576141381).


## Strongest consolidated theorem: one diagonal congruence

The preceding four disjoint congruence lattices have an unexpectedly simple exact equivalent condition:
\[
\boxed{\qquad j\text{ odd},\qquad m\equiv j+25\pmod{32},\qquad m\ge4.\qquad}
\]
For the original-source stopping equation \`k+j+3m+5=2^(2m+2)*(j+3)\`, this single condition is enough to prove \`run secNext time (some (5,1)) != some (2*j+3,k)\` for **every** time. [CThreeDiagonal.lean](CThreeDiagonal.lean) contains both \`four_classes_iff_diagonal\`, the biconditional of congruences for arbitrary j,m, and \`high_stop_odd_diagonal_mod32\`, the authenticated blank-root exclusion. This is an infinite diagonal congruence family with exactly **1/64 natural density**, independent of the stopping time. The formal source proof was separately compiled successfully in [Lean CI 42577934765](https://github.com/FlareZ123/bb6/actions/runs/42577934765) with no \`sorryAx\`. It is equivalent to the four branches above and does not imply Machine C nonhalting.

## Stronger complement: four source-excluded stopping lattices (9 November 2026)

**Original-source Lean 4.36.0-rc2 verified, [successful CI 42577477628](https://github.com/FlareZ123/bb6/actions/runs/42577477628).** This theorem supersedes the earlier two-lattice headline above. The full combined theorem is \`BB6.Agent4Three.high_stop_four_lattices\` in [CThreeAltStop.lean](CThreeAltStop.lean). Under the same exact original-source high-stop equation and m>=4, any of these four pair conditions excludes the authentic blank-root Machine C section target for all times:

\[
\begin{array}{c|cc}
&j\bmod8 &(j+3m)\bmod32\\ \hline
A&3&23\\
B&7&7\\
C&1&15\\
D&5&31
\end{array}
\]

Each infinite parameter lattice has density 1/256 of (j,m) pairs, so the disjoint union has density **1/64**. Explicit infinite lines: A (j=3,m=28+32r); B (j=7,m=32+32r); C (j=1,m=26+32r); D (j=5,m=30+32r). These are disjoint residue cylinders even when the stopping equation is imposed, because j modulo 8 differs.

The complementary sharp two-ancestor sector is \`T'=(8s+5,16t+12)\` for s%2=t%2. Its unique first parent is \`P'=(8s+16t+15,8t+5)\`; unique second parent is \`Q'=(4s+12t+8,2s+10t+5)\`. The second parent has odd right counter >=5 and coordinate sum \`6s+22t+13\` congruent to 1 modulo 4 under the parity condition, hence cannot be an original section output. The first two edges exist, source verified in [CThreeAltWit.lean](CThreeAltWit.lean). This supplies two additional disjoint strict I2-minus-I3 cylinders \`(x mod16,y mod32)=(5,12)\` and \`(13,28)\`, increasing the present four-cylinder section-coordinate density to **4/512 = 1/128**, without overlap with the first two cylinders.

All proofs use the unchanged original \`secNext\`, its unrestricted exact inverse, the source \`section_odd_image\`, and genuine blank section start. No bounded simulation or conjectural root assumption enters. The CI compiles [CThreeAltSource.lean](CThreeAltSource.lean), [CThreeAltStop.lean](CThreeAltStop.lean), and [CThreeAltWit.lean](CThreeAltWit.lean) alongside the earlier six modules, and verifies that no \`sorryAx\` appears in their printed theorem axioms.

**Novelty qualification:** The full generic affine even-right direct-predecessor lemma was already present in Agent15's earlier source formalization. The earlier source-certified missing-I2 rectangle (x%4=1,y%8=0,y>=16) is separate from the present I2-minus-I3 sectors, which all have y%8=4. The combined C/D parameter lattices were sampled against a transcription of the prior ValSixFull high sieve and all 512 tested pairs passed; full analytic admission to the latest integrated high sieve and nonimplication by Agent45's global I3 characterization require additional work. No claim of BB(6) determination.
