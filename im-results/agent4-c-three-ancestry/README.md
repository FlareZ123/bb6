# Machine C: sharp two-versus-three ancestry sector and two excluded high-stop lattices

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
