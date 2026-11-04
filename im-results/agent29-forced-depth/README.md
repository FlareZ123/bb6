# Machine C exact forced-inverse depth by weighted mass residue

**Agent 29, 2026-11-04.** Intermediate structural research. Machine C, the other six-state holdouts, and BB(6) remain open.

## Exact scope

The three unique predecessor gates are defined in the repository's **unchanged, original-source-certified** `im-results/agent3-c-bounce-inverse/FullForcedNormalize.lean` (original-source CI 41697210586). Here `M(x,y)=x+2y`, the order is odd/odd low-valuation (O), even/odd seven-sector (E), even-right affine (A), and the original guards are pairwise disjoint. They remove exactly 7, 7 and 4 from M respectively. Each forced edge is an exact section predecessor; arbitrary chains starting at synthetic inputs make no assertion about reachability from the true blank seed `(5,1)`.

The new source file [SourceBound.lean](./SourceBound.lean) states:

* `no_five_mass_one`: for all six natural-number pairs, five consecutive forced edges are impossible if the initial M is 1 modulo 4.
* `no_six_mass_zero`: for all seven natural-number pairs, six consecutive forced edges are impossible if initial M is 0 modulo 4.
* `four_is_sharp`: `(569,292564) -> (293131,146281) -> (219704,182991) -> (201345,192167) -> (196754,194459)` has guard word **A O E O**.
* `five_is_sharp`: `(6,113) -> (57,84) -> (139,41) -> (88,63) -> (73,67) -> (68,66)` has guard word **E A O E O**.

All displayed arrows are independently checked with an exact Python implementation of the unmodified source guard formulas. The four-step initial state is a legitimate **arithmetic second-family stopping input**, `j=283, m=4, k=292564`, satisfying `k+j+3m+5 = 2^(2m+2)*(j+3)`. It is *not* a demonstrated blank-orbit state.

**Original-source Lean verification:** a manual-only existing source workflow `.github/workflows/agent3-c-bounce-inverse.yml` now compiles `SourceBound.lean` directly after `FullForcedNormalize.lean`. The first run is [41765306252](https://github.com/FlareZ123/bb6/actions/runs/41765306252), dispatched from 8b365ca7. The proof is **CI pending**, and must not be described as kernel-verified until the run actually passes its source check and the final theorem axioms are inspected.

## Elementary modular mechanism

For M congruent 1 modulo 4, E cannot be the first gate, because E needs x even, y odd and x+y congruent 3 modulo 4, which forces M to be 0 or 2 modulo 4. The A branch preserves M modulo 4, and for M=1 its resulting first coordinate is odd and second coordinate is odd, so another A or E is impossible. An O step has an even first coordinate in its parent, ruling out a second O, while an A step requires an odd first coordinate and even right counter. The only potential long word in class M=1 is **A O E O**. This uses the exact E-O-E contradiction already in Agent3's `OddForcedDepth.depth_no_seven_odd_seven`, so its no-five argument does not need any finite search.

For M congruent 0 modulo 4, only E is initially possible. Its predecessor has M=1, proving no more than 1+4=5 gates. The explicit EAOEO example gives sharpness. The earlier Agent3 two-sector analysis excluded O/E-only words of length four; this three-sector classification allows longer A-inclusive words.

A separate modular screen of every initial pair `(x%4096,y%4096)`, retaining 4,194,304 representatives with M=1, yielded no five-step words, with 12,288 length-four representatives and word **AOEO**. This is independent finite corroboration of the universal proof, rather than its justification. The genuine source guards include minimum-size inequalities and natural subtraction; the proof module works directly on the exact naturals, not on a modular truncation.

**Additional exploratory observation, not yet source-verified:** the mass-2 sector appears to admit at most two consecutive edges, by the previously known E-O-E exclusion and the fact that initial M=2 forces E, while the resulting M=3/x-residue constrains the next gate to O. Mass-3 admits arbitrarily long A chains on synthetic states, via `(x0,y0)=(3, 2^(n+2)-2)`, which has exactly n consecutive affine predecessors and ends with right counter two. A complete source proof of this phase diagram and its application to surviving genuine halting families remain next steps.

## Limits and next research action

These are sharp **forced-normalization bounds**, not a classification of all Machine C predecessors and not a nonhalting argument. Existing source-certified `FullForcedNormalize.blank_reach_iff_fullForcedNormalize` guarantees reachability equivalence only after the actual forced prefix. Inverse branches after that residual may remain unresolved.

After the source check succeeds, prove the exact equality of the recursively defined `fullForcedNormalize` with its four- and five-step fuelled versions for classes 1 and 0, respectively; then integrate with Agent15's two complete stopping families and the existing full forced exclusion filter. The true difficult sector is second-family j even, m odd, M congruent 3, where affine depth can grow with 2-adic valuation. Independently review prior-art overlap before promotion to `results/`.
