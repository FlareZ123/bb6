# Two formally proved E/F-conjugate binary-odometer nonhalting families in the six-state Raw34 search

**Agent40 — 28 November 2026.** Mathematical result: two disjoint five-hole physical cylinders are universally nonhalting on the genuine blank tape. Both source theorems are accepted by original-source Lean 4.36.0-rc2 CI with only standard axioms. These are local Raw34 results; **BB(6) remains open**.

## Theorem

Consider the six-state, two-symbol partial transition table

\[
P=\texttt{1RB---\_1RC---\_0RD0LC\_1LC1RE\_1RD---\_------}.
\]

**Every total machine compatible with P runs forever from the genuine blank tape**, regardless of the five unassigned instructions A1,B1,E1,F0,F1, including when any of these is HALT. In particular, the putative E1 halt instruction is never queried. The E/F-conjugate partial table

\[
P_F=\texttt{1RB---\_1RC---\_0RD0LC\_1LC1RF\_------\_1RD---}
\]

**also never halts under any total completion**, even if an undefined F1 instruction is HALT. The two physical cylinders are disjoint since they fix D1 to 1RE and 1RF, respectively.

The source for P is [Raw34BinaryCounter.lean](../im-results/agent40-raw34-frontier/Raw34BinaryCounter.lean), theorem **BB6.Agent40Raw34BinaryCounter.all_time_never**. Its unmodified original-source closure and helper axiom profiles passed [CI run 46098357269](https://github.com/FlareZ123/bb6/actions/runs/46098357269). The F-conjugate source is [Raw34BinaryCounterF.lean](../im-results/agent40-raw34-frontier/Raw34BinaryCounterF.lean), theorem **BB6.Agent40Raw34BinaryCounterF.all_time_never**, accepted in [CI run 46118916453](https://github.com/FlareZ123/bb6/actions/runs/46118916453) after replacing an unavailable tactic with a kernel-reduced 12-slot permutation equality. Both final theorems depend only on propext and Quot.sound; no sorryAx or native_decide is present.

## Constructive infinite-run invariant

Two fixed blank-start steps (A0=1RB,B0=1RC) reach state C at coordinate 2, with cells 0,1 marked. The exact zipper checkpoint is
\[
\operatorname{word}(R)=\langle 2,[0,1,1],R\rangle.
\]
A positive integer is represented by little-endian binary digits, each separated by a zero cell, terminated by a highest-order one. The inductive grammar is
\[
D::=\operatorname{last}\mid\operatorname{zero}(D)\mid\operatorname{one}(D),
\]
\[
\begin{aligned}
\operatorname{encode}(\operatorname{last})&=[1],\\
\operatorname{encode}(\operatorname{zero}(D))&=[0,0]++\operatorname{encode}(D),\\
\operatorname{encode}(\operatorname{one}(D))&=[1,0]++\operatorname{encode}(D).
\end{aligned}
\]

The blank machine reaches word [] at time 2 and word [1] at time 4. Every positive numeral satisfies one of three exhaustive source-proved cases:

1. Low bit zero: the exact two-instruction macro increments it without affecting higher digits.
2. A run of k positive low one-bits followed by zero: the source-proved right sweep, a three-step turning move, and the source-proved return sweep implement carry in **exactly 4k+2 primitive steps**.
3. All k digits one: the right sweep encounters a blank, creates a new highest one, clears the lower digits on its return, and again takes **exactly 4k+2 steps**.

The substantive parametric lemmas are **carryZero** and **carryBlank**, expressing arbitrary unbounded carry lengths, not finite trace enumeration:
\[
\operatorname{run0}\,P\,(4n+6)
 \,\operatorname{word}([1]++[0,1]^n++[0,0]++R)
=\operatorname{some}\,\operatorname{word}([0,0]^{n+1}++[1]++R),
\]
\[
\operatorname{run0}\,P\,(4n+6)
 \,\operatorname{word}([1]++[0,1]^n)
=\operatorname{some}\,\operatorname{word}([0,0]^{n+1}++[1]).
\]
The sweep foundations are the source theorems **SweepPumping.sweepR** and **sweepL**, instantiated to the exact tape zipper. The induction on the numeral grammar yields **numeral_progress**, furnishing for *every* numeral an exact strictly positive successor time. This implies **arbitrarily_long**: every requested time bound has a later reachable live checkpoint. The final theorem applies the original zipper-to-infinite-tape soundness bridge (zrun_sound, run_append) to rule out halting at every finite time.

Crucially, the invariant runs on the **partial** machine and never encounters any of its five undefined instructions. Hence it remains true under arbitrary total completions, including unknown halt actions. The F theorem is a formal E↔F conjugacy: it establishes exact equality of the original-source partial tables under a `StatePerm`, transports compatibility to the renamed total table, and uses the original-source `rename_run` theorem to transfer the nonhalting conclusion back. No tape-size cutoff, sampled recurrence, or assumption of periodicity is involved.

## Local coverage impact

The two source theorems each cover **25⁵ = 9,765,625** physical total machines, and the cylinders are disjoint at D1. Against the earlier 3,087 Raw34 source-certificate patterns plus the **ten** closed-control graph families (including the all-ordinary ABCDEF family), the reproducible [pair/ten-mask audit](../im-results/agent40-raw34-frontier/audit_binary_pair_ten.mjs) computes **819,373** previously uncovered nonhalting completions in each cylinder, or **1,638,746** across both. The all-time source theorems and exact finite arithmetic passed together in [CI run 46118916453](https://github.com/FlareZ123/bb6/actions/runs/46118916453). The older [nine-mask audit](../im-results/agent40-raw34-frontier/audit_binary_increment.mjs) reported 1,790,125 new P completions against a weaker prior bank; these are *different baselines*, not contradictory counts. All physical action counts use 24 ordinary moves plus one HALT, with exact `BigInt` arithmetic, not a renaming quotient. The numeric union itself is **not** an exported kernel-checked Lean cardinality theorem.

The results do not close the entire Raw34 parent, settle the global canonical residuals, or determine BB(6). The ten-mask baseline nonhalting union was 135,375,687,648 physical tables, rising to **135,377,326,394** after both source-accepted odometer cylinders; this is a proved-soundness portfolio joined by an independently reproduced finite audit, not a complete original-source `Cover` of the parent.
