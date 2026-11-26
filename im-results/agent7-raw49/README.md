# Raw49: four unbounded sweep families and a canonical local cut

Parent: `1RB---_1RC---_0RD---_1LD1RC_------_------`. At step 6, the blank orbit first queries C1. Four disjoint subfamilies are nonhalting for every completion:

- C1=0RC.
- C1=0RA, A1=0RC.
- C1=0RB, B1=0RC.
- C1=0RE, E1=0RC.

The common zipper family is C with nearest-first left list 111 (including the scanned symbol) and right list of 2n+1 ones. It is reached at step 6 for n=0. A rightward sweep erases pairs of ones (directly, or through the selected relay state); C0 enters D on a blank, then D0 rewrites the erased interval to ones while moving left. D1 turns right to C. The exact epoch length is 4n+8, and the next configuration belongs to n+1. The induction is independent of every unspecified slot.

`Raw49Sweep.lean` proves growth and universal NeverHalts with the repository SweepPumping semantics. The four subfamilies cover 25^6 + 3*25^5 = 273437500 distinct literal completions; this is not a count of quotient representatives or a full parent closure.

`Raw49Cut.lean` integrates them with an audited two-query canonical tree. The original finite audit leaves 125 open canonical cylinders; the four symbolic families reduce that list to 121. The theorem parent_cut states that every TNF-quotient-compatible machine satisfies WeightedBound 7014 or belongs to the explicit remaining list. It neither assumes the remaining cylinders safe nor asserts a global reduction.

Local Lean 4.36.0-rc2 compilation used the existing Canonical77 artifact 14997966221 and CanonicalPartial.lean (repository blob 0542d92dfb937b630dfd24d11983aa3c826e911a). Axioms for growth and never: propext, Quot.sound. Axioms for parent_cut: propext, Classical.choice, Quot.sound. Count uses propext. No sorry. A source-rebuild CI acceptance is still needed before treating this as part of an accepted global Cover.

## Complete local child covers

Two five-hole children of C1=0LA now have zero canonical residuals and locally kernel-checked WeightedBound 7014 for every compatible completion:

| Index in initial open list | Fixed A1 | Local proof | Open leaves after finite cut |
|---|---|---|---|
| 0 | 0LB | Raw49C0All.all_quotient | 14 = 13 FAR + 1 exact alternating sweep |
| 5 | 1LB | Raw49C5All.all_quotient | 21 = 21 FAR |

The exceptional C0 leaf is 1RB0LB_1RC0RE_0RD0LA_1LD1RC_1LF0RF_1LA---. Raw49Alternating.lean proves at step 70 that F has left [0] and right (10)^3 1; each 40n+100-step epoch grows the exponent by two. Thus every F1 completion is nonhalting.

Raw49Progress.refined integrates both complete children, with exact 119-element complement, locally compiled. Three further one-hole exceptions in C2 (A1=0RA) have exact Lean-checked growth in Raw49ThreeSweeps.lean, at costs 6n+29 and 12n+29 (two variants). The C2 assembled cover is still pending local compilation at this checkpoint. Candidate FAR witnesses for all other C2 open leaves are retained.

Reproduce generated child modules with bash prepare.sh /tmp/raw49-generated from this directory. The generator adapts Agent 19's canonical audit/finite automaton proof pattern; FAR evidence is from the existing farbank.cpp, and cut.cpp is a depth-limited canonical adaptation of Agent 2's trace classifier. The generators are untrusted; the Lean theorems require canonicalCheck and empty residuals. Generated modules are intentionally not committed. Source-rebuild acceptance and a global parent removal remain pending.
