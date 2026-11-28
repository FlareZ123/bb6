# Agent 50: Raw34 radius-two finite-window domain families

**Status (2026-11-28 UTC): source theorem and 128-mask proof-bank checks
submitted to original-source Lean CI, not yet accepted.** The numerical
results below are deterministic finite computations until that gate passes.
Do not fold them into the public accepted portfolio prematurely.

## Mathematical construction

Let `P(q,L2,L1,c,R1,R2)` be a Boolean predicate on a control state and
the five **actual** tape cells centered at the head. For a physical
ordinary instruction, both possible newly entering tape values must
produce another observation in `P`. For an unreachable state/symbol
slot the instruction is arbitrary, including a genuine HALT instruction.
If the blank observation satisfies `P`, this property is an inductive
invariant of the original infinite tape. Hence **every** total machine
satisfying these per-slot permitted-action restrictions is nonhalting.

`Window5General.lean` projects a radius-two invariant onto the
already-original-source-proved Agent 18 nine-cell abstract step; it proves
the all-completions `NeverHalts` rule for a partial machine. The stronger
`Window5Domains.lean` proves the full action-domain rule for arbitrary
total machines. All possible newly entering cells are quantified; there
is no bounded-tape, blank-tail, or time cutoff premise.

For a five-cell finite predicate, the permitted action set for a slot
is independently computable by examining its at most 16 input
neighborhoods and both new boundary bits. These sets form a Cartesian
product over the 12 physical state/symbol instructions.

## Source-level proof targets

- `Window5Witness.lean`: a 33-window finite witness for
  `1RB1RD_1RC0LE_0RD1RE_1LC1LA_---1LC_------`,
  with E0/F0/F1 unassigned. Radius-one abstraction fails at still-free
  E0; radius-two closes all transitions.
- `Window5Product.lean`: a single 33-window invariant for 12 disjoint
  four-hole parents with A1/E0/F0/F1 free, B1 in
  `{0LE,0RD}`, D1 in `{1LA,1LC}`, E1 in `{0RD,1LC,1RC}`,
  and C1 fixed to `1RE`. Physical union cardinality:
  `2*2*3*25^4 = 4,687,500`.
- `Window5Domains.lean`: a larger mask
  `0xf000f000fffffffffffffccccccccfcc00000001`, requiring the
  original Raw34 A0/B0/C0/D0 entries and allowing respectively
  `6,6,8,25,25,8,25,25` actions at D1,C1,B1,A1,E0,E1,F0,F1.
  This yields `900,000,000` physical Raw34 tables; most were already
  certified by prior mathematical techniques, and this **is not**
  900 million fresh classifications.
- `Window5Bank128.lean`: finite source root checks for 128 distinct
  masks, plus a uniform nonhalting theorem for the associated
  physically permitted-action domains.

## Reproducible finite experiments and exact physical union

`search_and_count.mjs` performs a deterministic 250,000-trial
xorshift32 scan (seed 987654321) of Raw34 source compatible complete
machines with E0/F0/F1 set to HALT, branch action alternatives sampled
for A1/B1/C1/D1/E1. Each five-cell BFS exposes **both** possibilities
for newly entering tape values. It retains 128 promising distinct
inductive masks, and **recomputes** `mask-bank-128.json`, including
candidate tables, 25-bit action domains, and baseline marginal counts.

`audit_mask_bank_union.mjs` constructs an independent reduced,
25-ary decision diagram and computes the **exact union** of the 128
permitted-action products with the older 3,087 source-accepted
cylinders and nine accepted closed-control families:

| Physical Root34 subcubes | Count |
| --- | ---: |
| Earlier 3,087 + nine graph families | 123,226,284,000 |
| Their union with 128 radius-two families | 123,277,683,300 |
| Candidate incremental gain over that older bank | **51,399,300** |
| Total fixed-Raw34 complete tables | 152,587,890,625 |

These are exact 25-outcome combinatorial counts with HALT distinct.
The **51,399,300** is only a difference against the stated older bank.
Newer Agent 40/23 F/E rays, side cycles, depth-five and depth-six
source-certified families are not subtracted from this comparison;
the latest-union incremental number must be computed before
reporting any *current-frontier* gain.

The opt-in `--include-window5-mask-bank` flag in
`../agent40-raw34-frontier/rank_live_nonD1RD.mjs` reuses the
current exact-source MDD without changing ordinary runs, and the
new `raw34-window5-fullunion` manual CI workflow compares the 128
families against the fuller accepted bank.

## Limits and next research task

The classifier only uses sufficient local inductive invariants and
does not establish a complete Root34 `Cover`. It does not imply any
new universal BB(6) upper bound, nor resolve the 39 remaining
conditional global `Cover` obligations. The relevant next questions
are (a) how many of these 128 domains survive the **newest**
source-certificate union, and (b) how to use those verified domains
inside a source-checked complementary decision tree, prioritizing
still-live branch states rather than collecting redundant intervals.

Do not promote these computations to `results/` unless original
source Lean+axioms and the full finite arithmetic are accepted.
