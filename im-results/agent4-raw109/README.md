# Raw109 first-hole refinement and score-B consumer

Parent raw109, `1RB---_1RC---_0RD---_1LD1RE_---1RB_------`, is a retained canonical residual (six holes, 25^6 = 244,140,625 compatible completions). The first unassigned query is B1 at ordinary step 7. **The complete parent remains open.**

## Current candidate partition

Eleven ordinary B1 alternatives have immediate side-cycle certificates; the halt alternative is bounded by the root query. Twelve of the thirteen remaining alternatives have complete candidate trees in [specs.json](specs.json), with a common proposed bound 1703, consumed by [Raw109Refinement12.lean](Raw109Refinement12.lean). The last alternative is B1=0LF.

| B1=0LF candidate tree | Count |
| --- | ---: |
| Split nodes | 1,314 |
| Side-cycle leaves | 23,675 |
| Last-hole leaves | 4,931 |
| Initial open leaves | 1,617 |
| Pooled FAR witnesses | 1,428 |
| N-gram candidates (width ≤12) | 104 |
| Single-block sweeps | 46 |
| Long-epoch sweeps | 5 |
| New explicit FAR witnesses (5–6 states) | 13 |
| Unresolved leaves | 21 |

The exact enumeration was reproduced with the existing C++ generator algorithm and an independent JS implementation: open-list SHA256 `413916c71af62ae660bf5feb4939bf663d7e0706a0c7e0b210d341f00c79455a`; maximum weighted query bound 904, first query (8,F1). All 21 remaining leaf tables and the candidate indices/codes are recorded in the 0LF spec. Each is a one-hole table. The 17 with F0=0LB exhibit nested left growth, three others (1334,1404,1452) exhibit unary right-boundary expansion with internal counter phases, and 1475 exhibits a different bidirectional growth pattern. These are observations, not decisions.

**Proof status:** all 0LF additions are candidate-generation results. FAR and n-gram fixed points were computed; the existing symbolic sweep algorithm found the 51 sweep witnesses. The full original-source Lean compilation, local exception proofs, and source-accepted parent closure are not established. The existing generator will preserve all 21 unresolved leaves as explicit hypotheses. No roster entry may be deleted on the strength of this census.

The following sections preserve the earlier mathematical constructions and candidate partitions; their intermediate remaining-branch counts are superseded by the current candidate partition above.

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

### Additional candidate closures: 1LB and 0RF

The pooled FAR bank and n-gram search leave three 1LB leaves (23, 240,
1926) and five 0RF leaves (52, 389, 391, 396, 410). Existing sweep
generation covers 1LB/23,240 and 0RF/52,391,396,410. The period-two
left-boundary sweep for 1LB/1926 starts at t=34, grows by 12 ones per
return, and is emitted by the long-epoch generator. 1LB/25 has a
width-12 n-gram certificate.

For 0RF/389, the new Raw109RF389.lean proves an exact nested unary
growth recurrence. Write A(N) for state A, empty left zipper, right
0 followed by N ones. From blank, A(4) is reached at t=17.
For even N>=2, entry goes to C with N+1 zeroes and two ones.
Every inner C phase trades one zero for three ones at cost 2k+10,
and the final left sweep transfers two ones per six steps. Consequently
A(N) reaches A(3N+4) in positive finite time. Lean 4.36.0-rc2 checked
all recurrence and induction theorems against a verbatim local copy
of the original zipper semantics and composition lemma; only
propext and Quot.sound occur in the arbitrary-prefix theorem.
The complete original-source bridge remains subject to CI.

New candidate upper bounds: 1LB 127 (2123 FAR, 6 n-gram, 3 sweeps);
0RF 461 (487 FAR, 6 n-gram, 4 sweeps, 1 nested-growth proof).
Together with the earlier four children, this leaves seven of the
25 B1 choices (68,359,375 completions) under the proposed bound-461
partition, and resolves 175,781,250 completions if accepted.
Raw109Refinement6.lean gives the corresponding candidate 84-entry
canonical-roster graft. No complete cylinder is claimed accepted yet.

### Seventh candidate branch: 1RF

All 699 initial open leaves now have concrete candidate certificates:
689 pooled FAR, one additional exact five-state FAR (leaf 312, code
00102340103), one n-gram (582), four one-block sweeps (293, 362, 387,
599), one long-epoch sweep (570, period four, entry t=8), and three
new hand-derived proofs. The additional DFA is recorded against its
exact table in specs.json and goes through the same mask closure and
kernel checker as pooled FAR certificates.

- Raw109RF506.lean handles both 506 and 508 with a single Boolean
  table parameter. At state F, left word 0 1^(4n+4) 0 L and empty
  right zipper, one epoch increases n by one and prepends 1 to L.
  Costs are 16n+25 and 16n+27; entries t=33 and 35.
- Raw109RF3.lean uses a regular inductive code of triples b11 and
  seven terminal words of length 2–4. A carry across b=0 advances
  three cells, clearing b=1 returns to the sentinel, and the all-zero
  terminal cases regenerate a unary F configuration. The Safe
  invariant is inhabited at t=50 and has a positive live successor
  at every element. This proves unbounded live prefixes without
  enumerating the exponentially many counter values.

Both arbitrary-prefix proofs checked locally in the same Lean 4.36.0-rc2
zipper harness, with only propext and Quot.sound. The original-source
NeverHalts bridges, combined tree, and global graft are still candidate
integrations. The 1RF bound is 268.

### 1LC candidate

All 430 residual leaves accounted for by 420 bank FAR, 4 n-gram, 2 single sweeps, 2 multi sweeps, and the paired 354/356 inductive certificate in Raw109LC354.lean. The arbitrary-prefix theorem checked locally with only propext and Quot.sound. The proposed bound is 162. The 82-cylinder refinement retains five B1 choices: 0LA, 0LF, 0RC, 1LA, 1LF. Original-source audit pending.

### 0LA candidate

691 residual leaves: 643 bank FAR, 38 n-gram, 4 single sweeps, 1 multi sweep, and five manual digit-grammar certificates (142,472,515,524,529). All four handwritten arbitrary-prefix theorems passed Lean 4.36.0-rc2 locally, with propext and Quot.sound only; the original-source bridge and full tree still require CI. The leaf 515 construction proves a sweepable-word reverse relation and a unary prefix increment of two per epoch. Proposed bound 168. Refinement9 retains only 0LF, 0RC, 1LA, 1LF, giving a conditional 81-cylinder global roster.
