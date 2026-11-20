# Suffix-extended halting cylinders from the external 108-step proof

**Status:** the final E-tail computations and their finite-window transfer are Lean-kernel checked in `TailWindowCore.lean` and `TailWindowResults.lean`. A source-level proof draft for the 107-call arbitrary-suffix prefix endpoint is now in `SuffixParametricPrefix.append.lean`; the existing manual workflow has been extended to compile it against the pinned upstream source, so that endpoint is not yet accepted until CI succeeds. The full additional halting cylinders remain conditional. Keep this in `im-results/`; do not promote it to `results/` yet.

## Reduction

The pinned external theorem proves that
`A(3^108*k + C, [])` halts, where
`C = 1975700577069254261393123959451562008800234946348086`.

The 107 `A_step2` calls are built from `step_An_1101` lemmas with an arbitrary suffix parameter. Their endpoint for the empty suffix is
`A(3*8^107*k + C2, P)`, with
`P = [0,1,0,1,1,0,1,1]`.
The suffix-preserving composition can be replayed with an arbitrary initial suffix `r`; the corresponding endpoint should be
`A(3*8^107*k + C2, P ++ r)`.
The candidate proof is preserved in `SuffixParametricPrefix.append.lean`; it replaces the 11 intermediate `stepStar_halts` wrappers by `stepStar_trans` and carries the 107 existing `A_step2` calls unchanged. It states the arbitrary-suffix endpoint below. Its compile check is in the existing `agent32-cryptid-padding.yml` workflow, against upstream commit `b77dda5c79fb196d67ce35669e172ad632401c1b` and that source repository's Lean 4.36.0-rc1 toolchain.

Since `C2 mod 3 = 1`, the final `step_An_1101` takes its E branch. Its endpoint has:
- state E;
- scanned symbol `P.head = 0`;
- left stack `[0,0] ++ [1,0]^(4*(n/3)-1) ++ [1,1] ++ 0^∞`;
- right stack `P.tail ++ r ++ 0^∞`.

For the canonical DRegular suffix `r=(01)^q 1^b`, the final raw tail starts in E with current symbol 0, left stack `[0,0] ++ [1,0]^m ++ [1,1] ++ 0^∞`, and right stack `[1,0,1,1,0,1,1] ++ r ++ 0^∞`, where (m=4(n/3)-1).

## Kernel-checked final tails

- `TailWindowCore.lean` defines the exact D0 transition table, tape model, and generic finite-window equivalence/run-transport lemmas.
- `TailWindowResults.lean` proves the finite local traces and applies the window transport to the actual finite left stack `[0,0] ++ [1,0]^m ++ [1,1]` for every (m\ge3).
- The head-position bounds show that no positive trace leaves the first five left cells; the right tape is exact through the suffix and blank thereafter.

The wrappers `actual_empty_suffix_113`, `actual_suffix_01_127`, `actual_suffix_011_74`, `actual_suffix_0101011_131`, and `actual_suffix_010101011_153` prove that the D0 run reaches state F scanning 1, and the next step is undefined, for every (m\ge3).

| Canonical suffix r | q,b | Final raw steps to F/1 | Max head displacement right | Min head displacement left |
|---|---:|---:|---:|---:|
| empty | (0,0) | 113 | 10 | -5 |
| 01 | (1,0) | 127 | 13 | -5 |
| 011 | (1,1) | 74 | 12 | -2 |
| 0101011 | (3,1) | 131 | 16 | -5 |
| 010101011 | (4,1) | 153 | 18 | -5 |

The empty-suffix trace reproduces the external proof's 113-step tail exactly. The four extra cases are kernel-checked as final-tail lemmas for the explicit D0 table and actual left-stack shape.

`#print axioms` reports only Lean's core `propext`, `Classical.choice`, and `Quot.sound`; there are no project-specific axioms, `sorry`, or unproved hypotheses in the finite-tail development.

## Suffix-parametric prefix proof candidate

The new appended theorem has the target
[
 A(3^{108}k+C,ls)\;\vdash^*\;
 A(3\cdot8^{107}k+C_2,P++ls).
]
It reuses the upstream 107 `A_step2` invocations exactly; only the outer composition combinator changes from `stepStar_halts` to `stepStar_trans`, and the final halting tail is omitted. This is a direct source-level generalization because `step_An_1101`, the supporting lemmas, and `A_step2` all quantify over and preserve the arbitrary suffix. The source file is pinned to upstream commit `b77dda5c79fb196d67ce35669e172ad632401c1b`.

The updated existing manual workflow appends this theorem to the pinned source file and compiles the complete file. A successful run will certify the arbitrary-suffix prefix endpoint; until then, treat it as a draft, not a theorem.

## Conditional full-cylinder consequence

If the 107-call composition is formally generalized to preserve an arbitrary suffix as `P ++ r`, the four extra final-tail lemmas yield:
[
 A(3^{108}k+C,(01)^q1^b)\text{ halts}
]
for ((q,b)=(1,0),(1,1),(3,1),(4,1)), in addition to the existing ((0,0)) case.

This is a conditional consequence until the parametric 107-call endpoint and the source TM62-to-D0 transport are composed in Lean. The final-tail part itself is no longer merely a simulation.

## Why this matters to the D-root program

The suffixes ((01)^q1^b) are exactly the canonical DRegular suffixes used by `L(a,q,b)`. The external halting cylinder therefore need not be restricted to the pure-unary section `q=b=0`: it also supplies candidate halting classes at `q,b=(1,0),(1,1),(3,1),(4,1)`, all at the same unary residue (a\equiv C\pmod {3^{108}}).

The D-root exception table in `im-results/agent2-root-language-exit/seed31-38-exact-replay.md` has:
- (8,1), residue 39637;
- (1,1), residue 58126;
- (5,1), residue 49579;
- (6,1), residue 55039;
- (9,1), residue 54265;
- (7,1), residue 27469;
- (6,1), residue 50584;
- (1,1), residue 24670.

But (C\bmod 59049=23839). None of these eight exceptional states is in any of the candidate cylinders, already at the weaker modulus (3^{10}=59049). In particular, the two known q=1,b=1 root exceptions are not hits of this specific C-cylinder. This is an exact low-modulus exclusion for those listed exception states, not an all-time exclusion of the root orbit.

The new cases (1,0), (3,1), and (4,1) are worth checking against regular intermediate states and later root episodes, not just exceptional endpoints. A root state in one of these suffix classes with (a\equiv23839\pmod{59049}) is a necessary first filter for the full (3^{108}) congruence.

## Reproducible search scope

A small simulation search over (0\le q\le20), (0\le b\le30), with a 2,000-step horizon found no further halting cases in that rectangle. This is only a bounded search; it is not a theorem that other suffixes do not halt. The five positive cases above are separately kernel-checked in the Lean files.

## Kernel-acceptance path for the full result

1. Obtain a successful compile of `SuffixParametricPrefix.append.lean` through the existing manual workflow, thereby accepting the arbitrary-suffix 107-call endpoint.
2. Compose that endpoint with the appropriate `TailWindowResults.actual_suffix_...` theorem (or port the same window lemma into the external TM62 type).
3. Compose the source TM62-to-D0 conjugacy/transport proof and audit the transitive axiom profile.
4. Only then treat the four extended cylinders as formal halting results.

This does not prove that the authentic blank-root orbit reaches any of these cylinders. It enlarges the finite set of kernel-checked final-tail targets that the root-reachability investigation can search for.
