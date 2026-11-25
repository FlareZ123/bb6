# Raw109 first-hole refinement and score-B consumer

Parent raw109, `1RB---_1RC---_0RD---_1LD1RE_---1RB_------`, is a retained canonical78 residual (six holes, 25^6 = 244,140,625 compatible completions). The first unassigned query is B1 at ordinary step 7. The complete parent remains open.

## Complete candidate children

| B1 | Weighted bound | Splits | Side cycles | Last-hole leaves | FAR | N-gram | Inductive |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0LD | 324 | 595 | 11,100 | 2,266 | 316 | 0 | 4 |
| 0RE | 353 | 392 | 7,433 | 1,474 | 108 | 0 | 2 |
| 0LC | 240 | 738 | 14,373 | 2,431 | 159 | 12 | 0 |
| 1RE | 119 | 445 | 7,997 | 1,569 | 667 | 2 | 1 |

The four finite first-hole trees use the existing zip checker, including exact weighted query and halt rules. All candidate open leaves are covered by explicit FAR, local-window, or inductive certificates rather than a finite simulation cutoff. The 0LC n-gram candidate widths are at most 11; the largest has 6,359 abstract quadruples. The two 1RE local-window certificates have widths 4 and 5. Generation pins each open-list SHA256, count, and exact first-query index in [specs.json](specs.json).

**Proof status:** prior 0LD and 0RE cut plus the new 0LC and 1RE full candidate trees still require the original-source Lean audit. [Raw109Refinement.lean](Raw109Refinement.lean) is the consuming draft: it retains exactly nine B1 alternatives and grafts their physical partition into the canonical78 quotient interface. It claims no accepted global reduction until the full import closure and transitive axiom audit succeed. The source target is the existing manual `agent10-four-hole.yml` target `raw109-refine`.

## Unbounded binary counter in B1=1RE leaf 238

Table `1RB1LC_1RC1RE_0RD1RF_1LD1RE_1LA1RB_---0LA` has one hole F0. The exact zipper entry is at primitive time 30, state A with head-inclusive left word 101110 and right word 1. Represent the little-endian digits by b000 blocks (possibly ending in one bit). A three-step entry into E initiates a carry; each leading one digit transfers four ones to the left in eight steps. At the first zero or implicit blank, E0 writes a one and returns A. A twelve-step left transfer converts each carried group of four ones into four zeros on the right, returning to the fixed left sentinel. Thus a carry through k leading ones takes exactly 20k+4 steps from A to A and implements binary increment, including overflow into implicit blank.

[Raw109RE238.lean](Raw109RE238.lean) proves the arbitrary-tail carry, four-cell sweep, all-word return, and unbounded live-prefix theorem. The entire recurrence through `arbitrary` compiled locally on Lean 4.36.0-rc2 using verbatim `run0`, `join0`, and `sweepL` definitions/proofs, with axioms [propext, Quot.sound]. The final original-source `never_of_live` wrapper and full child tree are awaiting the source audit; the local check does not establish the transitive original-source status.

The older six one-block sweep candidates use entry 2 and family C with left zipper 01(1111)^n1 for the four 0LD leaves (costs 29+24n, 25+20n, 25+16n, 21+12n). The two 0RE leaves use E with 0011(1001)^n1 (29+14n) and D with 001(1011)^n1 (22+12n).

## Exact retained complement

[Raw109Cut.lean](Raw109Cut.lean) contains eleven immediate side cycles and the halt branch, in addition to the first two candidate children. If the four children and the partition are accepted, the parent has a score-353 bound or lies in one of these nine disjoint five-hole cylinders:

`0LA, 0LF, 0RC, 0RF, 1LA, 1LB, 1LC, 1LF, 1RF`.

The explicit retained mass is 9*25^5=87,890,625, while 156,250,000 completions belong to the closed alternatives. The quotient consumer replaces one of the 78 addresses by nine, producing 86 obligations, without dropping any unmatched representative. It accepts remaining covers at arbitrary target B≥7014. These are proposed counts, pending the source-check of the exact table matching and the graft.

## Reproduction

Run `python im-results/agent4-raw109/generate.py 0LD 0RE 0LC 1RE` after the standard source unpack and sweep preparation; then use the shared chunk checker and strict closure compiler as in the manual workflow. The local direct Git clone failed DNS resolution; the toolchain reconstructed successfully, and the exact-source closure is delegated to the existing pinned CI target. No full raw109 decision or BB(6) upper bound is claimed.
