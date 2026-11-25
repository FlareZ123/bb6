# Raw58 first-hole refinement

Parent `1RB---_1RC---_0RD---_1LD1RE_---0RA_------` has six holes (244,140,625 completions). The first query is A1 at step 7. Candidate source audit reduces this parent to 12 five-hole children: 11 moving branches have short translating cycles, the halt branch is bounded, and the A1=0RE branch has a complete certificate candidate with bound 55.

For A1=0RE, exact first-hole enumeration yields 488 split nodes, 2,259 last-hole leaves, 8,715 short translating cycles and 251 remaining leaves. Of these, 250 admit FAR certificates; the final machine `1RB0RE_1RC---_0RD0LF_1LD1RE_1LC0RA_1LB1LE` admits the rightward cycle (entry 39, period 278, lower boundary -3). This was missed by the earlier 256-period search window. The maximum enumerated weighted score is 55. No finite simulation cutoff is used as a verdict.

Reproduce with `python im-results/agent4-raw58/generate.py` then compile Raw58Cut.lean and its original-source dependency closure (manual target raw58-cut in agent10-four-hole.yml). The generated source checks every cycle, FAR and weighted query; the checked result, not the generator, is authoritative. Status: candidate only until the source Lean job passes. The original local Git clone was unavailable (DNS); the Lean toolchain itself was successfully reconstructed.

If accepted, 13 of 25 first-hole cylinders (126,953,125 completions) are bounded by 55; 117,187,500 completions remain in the 12 listed children. This is a disjoint refinement of raw58, not a complete raw58 decision.

## Three more complete candidate children

| A1 | Candidate weighted bound | First-hole splits | Last-hole leaves | Short cycles | FAR | Sweep proof | Other |
|---|---:|---:|---:|---:|---:|---:|---:|
| 0RD | 120 | 495 | 2095 | 9254 | 33 | 3 | 1 binary-counter proof |
| 1LC | 156 | 589 | 3146 | 10265 | 132 | 5 | 0 |
| 1RE | 93 | 506 | 2264 | 9271 | 97 | 7 | 0 |

Every child contains 25^5 completions. The binary counter (global discovery index 1892, local 0RD open index 32) is the machine `1RB0RD_1RC---_0RD0LC_1LD1RE_1RF0RA_1LC1RE`. At E with a fixed left sentinel, the right list is a little-endian digit sequence with zeros separating successive bits. A true digit extends the carry by two steps; a zero or implicit blank switches it to true, clears the carried prefix with a two-cell sweep, and returns E in 8 further reset steps. The formal `Code` induction proves a positive return from every valid sequence and carry depth. Blank reaches E after 15 steps, so arbitrarily long live runs follow. The complete arithmetic/zipper proof through `arbitrary` compiled locally on Lean 4.36.0-rc2 against verbatim original run0 and sweepL definitions (standard axioms only); the raw-machine soundness bridge awaits original-source CI. Source file Raw58RD1892.lean.

New generator generate_more.py plus more.json emits three complete candidate proof trees. Raw58MoreCut.lean combines them with the previous cut, leaving nine five-hole children (87,890,625 completions) at bound 156. Run target raw58-more. All new full-cylinder claims remain candidate until source acceptance.

## Counter generalization

The pair-counter proof `Raw58PairCounter.lean` and six literal-table instances in `Raw58PairCases.lean` establish a shared unbounded binary countdown invariant on words of pairs `1b`: carry skips zero pairs, a positive digit is cleared, and an exhausted word grows by one pair of ones. The induction guarantees arbitrarily long live zipper prefixes independently of the duration of the counter. The core lemma and all six instance reductions passed local Lean against verbatim extracted zipper definitions; original-source bridge acceptance remains pending. These are candidate discharges for five A1=0RC and one A1=1LA hard leaf, not entire cylinders.

The initial A1=0RE closure and 12-child refinement passed [original-source CI 45520713972](https://github.com/FlareZ123/bb6/actions/runs/45520713972). The named refinement step completed successfully. The three additional child closures are still being audited by [45521202017](https://github.com/FlareZ123/bb6/actions/runs/45521202017).
