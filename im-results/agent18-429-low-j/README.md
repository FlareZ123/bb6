# Candidate exact low-J continuation chart for #429 (unproved formulas)

**Research status: computational conjectures only.** The original six-state machine has exact source-proved chart returns for `w+1≥2u` in [Agent18's canonical chart](../agent18-429-junc-canonical/README.md). This dossier investigates the previously uncovered region `w+1<2u`, writing `r=2u-w≥2`.

Original source table: `BB429PhysicalFrontier.prefix11`, machine `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. Program [explore_low_j.py](explore_low_j.py) runs the exact raw table on every nonzero cell of the infinite canonical `jTape u w`, with explicit blank outside its finite support. At the proposed time it compares the **entire finite set of one-cells**, state, and physical head against the candidate translated J tape. No local-window approximation is used.

## Candidate residue-class formulas

Each row conjectures `J_0(u,2u-r) → J_h(U,W)` after exactly `T` primitive instructions. `k` is a nonnegative integer subject to the restrictions shown. All target `W` and starting `w` must be nonnegative. The formulas have **no Lean theorem yet**.

| Offset r=2u-w | T (raw steps) | Successor U | Successor W | Head h |
|---|---|---:|---|---|
| `r=4k+2`, `k≥0` | `4u²+(14−16k)u+16k²−10k+61` | `0` | `4u+8−4k` | `−2u−3` |
| `r=4k`, `k≥1` | `4u²+(22−16k)u+16k²−26k+261` | `11` | `4u−4k−2` | `9−2u` |
| `r=4k+1`, `k≥1` | `4u²+(14−16k)u+16k²−6k+60` | `2k+4` | `4u−8k−2` | `−2u+4k+4` |
| `r=4k+3`, `k≥1` | `4u²+(6−16k)u+16k²+26k+146` | `2k+9` | `4u−8k−10` | `−2u+4k+10` |
| `r=3` (special) | `4u²+6u+26` | `0` | `4u+2` | `−2u−2` |

The test batch covered all `2≤r≤34`, with `u` in the first 17 admissible values after `ceil(r/2)` (capped at 35) whenever the candidate successor has nonnegative W; **554 original-table examples passed**. Cases with negative candidate W were skipped. This is an experiment only, and the table may fail for larger parameters.

Representative low-offset observations:

| r | Raw return (all u in the admissible tested interval) |
|---|---|
| 2 | `J(u,2u−2) → J(0,4u+8)` in `4u²+14u+61` steps |
| 3 | `J(u,2u−3) → J(0,4u+2)` in `4u²+6u+26` steps |
| 4 | `J(u,2u−4) → J(11,4u−6)` in `4u²+6u+251` steps |
| 5 | `J(u,2u−5) → J(6,4u−10)` in `4u²−2u+70` steps |
| 6 | `J(u,2u−6) → J(0,4u+4)` in `4u²−2u+67` steps |

One explicit boundary warning: for `r=7,u=4`, the generic `r=4k+3` target W would be negative and is inapplicable. A different J return was observed later at time 563. For `r=7,u≥5`, the candidate formula fits tested inputs. Such exclusions are essential before attempting a universal theorem.

## Route to rigorous proof

The quadratic term `4u²` and residue-controlled linear coefficients strongly suggest a common first scan and a finite family of right-boundary exit macros, analogous to the source-certified [high-zero](../agent18-429-high0/High0Source.lean) and [high-one](../agent18-429-high1/High1Source.lean) decompositions. First prove the simplest `r=2` and `r=3` all-u source zipper macros, then use the already-proved [canonical Junc translation](../agent18-429-junc-canonical/JuncCanonical.lean) to obtain a full original infinite-tape physical result. Prove an explicit preservation invariant before interpolating coefficients into unbounded parameters.

This research remains under `im-results/` because numerical agreement is not a universal mathematical proof. These prepared inputs say nothing yet about the authentic initially blank #429 orbit or BB(6).