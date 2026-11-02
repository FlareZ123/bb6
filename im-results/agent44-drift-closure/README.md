# Agent 44: finite-control directed drift certificate for six-state sparse coverage

**Intermediate proof infrastructure, original-source CI verified.** This extends the sparse proof-carrying coverage language with a general all-time nonhalting leaf for machines that walk into fresh blank cells. It is not a new undecided BB(6) root classification, numerical bound, or exact BB(6) result.

## The certificate

Source: [DirectedDrift.lean](DirectedDrift.lean). It imports Agent 8's unmodified `Frontier.lean` and therefore uses the same six-state, two-symbol, full bi-infinite tape, 25-choice transition-table, and sparse `Cover` semantics.

For a direction `dir` and a state-set predicate `states : Fin 6 → Prop`, let `DriftClosed m states dir` mean that every state in `states`, when reading zero, performs some nonhalting write (either 0 or 1), moves exactly in `dir`, and enters another state in the same set. If the initial state A belongs to `states`, then:

```lean
directed_drift_never (m : Machine) (states : Fin 6 → Prop)
  (dir : Bool) (hinit : states 0)
  (hclosed : DriftClosed m states dir) : NeverHalts m
```

Proof invariant: the entire half-line ahead of the head remains blank at every time, and the control stays inside the closed set. Each transition consults only a zero and advances into that unvisited half-line. This handles arbitrary writes and any finite state-transition graph in the closed set. It holds for **all time**, with no finite-prefix cutoff.

The sparse-table version `PartialDriftClosed p states dir` requires that the finite closure transitions already be assigned by `p`. The theorem

```lean
partial_drift_cover (p : PartialMachine)
  (states : Fin 6 → Prop) (dir : Bool) (B : Nat)
  (hinit : states 0)
  (hclosed : PartialDriftClosed p states dir) :
  Cover (DecidedBelow B) p
```

proves one real `Cover.leaf` for **every compatible completion**, independent of the ten or more unassigned slots.

## Concrete reproducible covered cylinder

`alternatingTable` fixes precisely A/0 = 1RB and B/0 = 0RA, and leaves the remaining 10 state/symbol slots entirely unassigned. `alternating_cover B` is the resulting authentic `Cover (DecidedBelow B) alternatingTable` certificate for any B, representing exactly `25^10 = 95,367,431,640,625` fully specified canonical machine completions. No equivalence-class division is assumed; all 25 choices per other slot are covered individually by the theorem. Both A and B read only fresh zeros along their actual run.

Unlike the existing 0RA/0LA self-loop leaf, this example changes states and writes ones. The general rule also permits any directed closed graph on up to six states. The [prefix-entry rule](PrefixDrift.lean) combines this invariant with the existing source-certified prefix-preservation machinery.

## Exact nonoverlapping coverage census

The self-contained [census.py](census.py) enumerates the prefix-free drift certificates by fixing only the zero-symbol transitions encountered on the unique finite control orbit from A. If this orbit first repeats after visiting exactly `k` distinct states, its states form a *canonical* sparse certificate. The first `k-1` successor states are all distinct; the last successor repeats one of the `k` visited states. Each visited state's write bit is arbitrary; all other `12-k` table slots have 25 independent choices.

Consequently, **per direction** the number of disjoint cylinders of length k is `P(5,k-1) · k · 2^k`. The two directions are disjoint. Every terminal cylinder covers exactly `25^(12-k)` complete canonical tables. The exhaustive recursive enumeration and this independent combinatorial formula agree exactly:

| Visited states k | Disjoint terminal cylinders (both directions) | Full tables represented |
|---:|---:|---:|
| 1 | 4 | 9,536,743,164,062,500 |
| 2 | 80 | 7,629,394,531,250,000 |
| 3 | 960 | 3,662,109,375,000,000 |
| 4 | 7,680 | 1,171,875,000,000,000 |
| 5 | 38,400 | 234,375,000,000,000 |
| 6 | 92,160 | 22,500,000,000,000 |
| **Total** | **139,284** | **22,256,997,070,312,500** |

Thus the sound directed-drift leaf applies to exactly **22,256,997,070,312,500 / 59,604,644,775,390,625 = 37.341044736%** of all `25^12` canonical tables. This is a count of *full transition tables covered by the proved family*, not a proportion of normal-form representatives or BB(6) undecided holdouts. The cylinders are disjoint because they record the unique zero-transition state path up to its first repetition. The fraction counts the union without any inclusion-exclusion or root-equivalence assumptions.

The count itself is verified by the reproducible standard-library Python census plus the elementary prefix-count bijection; no kernel-certified finite-set cardinality theorem is claimed. Every cylinder's **nonhalting implication** follows from the source-certified Lean theorem by instantiating its finite closed state predicate and fixed transitions. No massive 139,284-node `Cover` term has been assembled or checked.

## Additional closed zero-writer family and exact union

[DirectedDrift.lean](DirectedDrift.lean) also proves `partial_zero_writer_cover`: every visited control state writes **zero** when reading zero, with arbitrary independent left/right directions and arbitrary closed state transitions. The entire physical tape remains zero forever, so every completion is nonhalting. The concrete `alternating_zero_cover` has A/0=0RB and B/0=0LA, a true direction reversal which the uniform-directed theorem cannot handle.

The [expanded census](census.py) independently enumerates the prefix-free zero-writing orbit certificates and applies exact intersection accounting with the fixed-direction family. At each orbit length `k`, let `P(5,k-1)=5!/(6-k)!`:

- Directed: `2 · P(5,k-1) · k · 2^k` cylinders.
- Zero-writer: `P(5,k-1) · k · 2^k` cylinders.
- Intersection: `2 · P(5,k-1) · k` cylinders (all writes zero, common direction).

The **union** has **205,664** canonical disjoint cylinders and covers exactly **26,171,093,750,000,000 / 25^12 = 43.907809280%** of all complete canonical tables. Restricting to the normalized exactly-one-halt population, the same two sound nonhalting classes cover **7,226,311,367,983,104 / (12·24^11) = 39.574165501%** of those tables. The numerical census is arithmetic plus Python enumeration, and is reproducible by `python im-results/agent44-drift-closure/census.py`. It is **not** a kernel-checked count of `Cover` instances; the individual soundness schemas are kernel verified.

[Manual CI 41504224825](https://github.com/FlareZ123/bb6/actions/runs/41504224825) compiled the *unmodified original* `Frontier.lean` and both `DirectedDrift.lean` theorem families with standard axioms only.

## Finite-prefix entry beyond the two closed families

[PrefixDrift.lean](PrefixDrift.lean) proves `prefix_drift_never`: if an actual finite blank-origin run reaches a state in a fixed-direction closed graph, while its unexplored forward half-line remains blank, then the **entire** blank-origin run never halts. Its sparse counterpart `prefix_drift_cover` demands that the finite entry prefix consult only already-assigned sparse transitions, via Agent 8's unmodified `common_prefix_of_partial_table`. This can close search nodes even if the early transitions change direction or write/revisit marked tape cells. The original-source dependency chain and both prefix theorems compiled successfully in [manual CI 41504835085](https://github.com/FlareZ123/bb6/actions/runs/41504835085).

[TransientExample.lean](TransientExample.lean) gives a concrete four-rule case: A/0=1RB, B/0=0LA, A/1=0RC, C/0=1RC. Three genuine steps bring the blank machine to C scanning zero, with an entirely blank physical tape, after a direction reversal and a revisited 1. From then on it writes 1 while drifting right in C. The 25^8 compatible full tables are all nonhalting. These tables are **disjoint** from the earlier two families, because A/0 and B/0 reverse directions and A/0 writes 1. Its final `transient_drift_cover` **passed original-source CI [41505253066](https://github.com/FlareZ123/bb6/actions/runs/41505253066)**, compiling unchanged Agent 8 `Frontier.lean`, the previous source-certified prefix theorem, and the exact finite-entry certificate with only ordinary Lean axioms.

## Source-certified four-step physical-tape bounce cycler

[BounceCycle.lean](BounceCycle.lean) imports the existing original Agent 8 `LeafRules.cycle_leaf` theorem. It fixes A/0=1RB, B/0=0LA, A/1=0RB, and proves that the literal blank-origin run returns after exactly **four genuine primitive steps** to the exact same starting `Config`, including every physical cell of the bi-infinite tape. Only these three sparse slots were consulted during the first four transitions. Therefore `bounce_cover B` is an authentic `Cover (DecidedBelow B) bounceTable` for all `B`, regardless of the nine unassigned transitions.

[Manual CI 41505951766](https://github.com/FlareZ123/bb6/actions/runs/41505951766) compiled the **unmodified original** `Frontier.lean`, `OneHalt.lean`, and `LeafRules.lean` before the full `BounceCycle.lean` source and completed successfully; its axiom audit prints ordinary Lean axioms only, with no `sorryAx`. Local signature-compatible mock use was preliminary and superseded by this upstream-source check.

The bounce cylinder covers exactly `25^9 = 3,814,697,265,625` canonical completions; it is **disjoint** from the two zero-symbol-control closure families because it reverses direction and writes 1, and disjoint from the finite-prefix drift example because the required A/1 target differs (B versus C). Its nonhalting proof uses the existing sound general cycle decider instead of requiring a new mathematical theorem.

## Combined proven cylinder count and limits

Taking the pairwise disjoint transient-entry and bounce examples together with the exact union of the two large closure families, the **four original-source-certified certificates** cover

- **26,175,061,035,156,250 of 59,604,644,775,390,625** full canonical six-state tables, or **43.914465280%**.
- **7,227,338,737,582,080 of 18,260,173,718,028,288** exactly-one-halt canonical tables, or **39.579791787%**.

These exact arithmetic counts use the independent Python census, the distinct fixed-table patterns, and `25^u` or `u·24^(u-1)` for `u` remaining unassigned slots. The combinatorial cardinality calculation itself is not a Lean theorem. **Every nonhalting implication is original-source kernel-checked.** The percentages are counts in the unnaturally broad all-tables space, not measures of progress toward classifying the outstanding BB(6) holdouts. A complete universal `Cover (DecidedBelow B) emptyTable` remains absent.

No claim is made that these certificates constitute a single universally completed `Cover` object, a new machine decision, or a solution of BB(6).

## Executable oracle integration with Agent 8

Agent 8 independently developed [`RayOracle.lean`](../agent8-coverage-contract/RayOracle.lean), which decides the same fixed-direction fresh-zero ray family using an executable search of 64 state subsets and produces an actual `Cover` object. The prefix-entry theorem in [`RayEntry.lean`](../agent8-coverage-contract/RayEntry.lean) likewise overlaps our independently obtained [`PrefixDrift.lean`](PrefixDrift.lean). Future work should reuse Agent 8's executable implementations and avoid multiplying redundant theorem variants.

Our **complementary** [`ZeroWriterOracle.lean`](ZeroWriterOracle.lean) defines:

```lean
zeroWriterOracle (p : PartialMachine) : Bool
zeroWriterOracle_sound (p : PartialMachine) (bound : Nat)
  (h : zeroWriterOracle p = true) : Cover (DecidedBelow bound) p
```

For each six-bit state mask, it checks that A belongs to the mask and every state in it has an already assigned nonhalting zero-writing zero-reading transition returning to the mask, with no direction restriction. The proof `zeroMaskCheck_sound` translates accepted Booleans into our source-certified tape-blank invariant. The six-state mask search is exhaustive over this predicate.

[`UnifiedNonhaltingOracle.lean`](UnifiedNonhaltingOracle.lean) combines the two source-certified Boolean checks into one usable `basicControlOracle p := rayOracle p || zeroWriterOracle p` and theorem `basicControlOracle_sound`. Its same-source integration was **verified successfully** by [manual CI 41507584847](https://github.com/FlareZ123/bb6/actions/runs/41507584847), which compiled **unmodified original** `Frontier`, `RayClosed`, `RayChecker`, and `RayOracle` before both new checker modules. Both final source certificates have no `sorryAx`; they yield genuine infinite-run leaves over every compatible full table.

The exact combined all-table coverage of the two oracles is **43.907809280%**, an increment of **6.566764544 percentage points** from zero-writer graphs not already included in Agent 8's 37.341044736% ray oracle. This is an all-transition-table census, not a percentage of classified outstanding BB(6) machines. To consume the oracle in a proof-producing sparse search, evaluate the Boolean on a partial table; when it is true, invoke `basicControlOracle_sound`.

[`FastZeroWriter.lean`](FastZeroWriter.lean) is an optional cheaper candidate check: follow seven deterministic zero-successor edges to construct one candidate mask, then use the exact same `zeroMaskCheck`. The theorem `zeroWriterFastOracle_sound` proves **soundness** on acceptance; **completeness against the 64-mask oracle is not formally shown**, so a `false` result must be treated as inconclusive. This file awaits the current full-source CI run; no speedup figure is claimed without a runtime benchmark.

## Reached, unresolved transition and a heterogeneous 25-way branch

[`MixedTwentyFive.lean`](MixedTwentyFive.lean) defines a partial table with A/0=0RB, assigned B/1 halting, assigned C/0 through F/0 halting, and B/0 **unassigned**. Thus the first unresolved slot is genuinely read after the first ordinary move. For every choice among its 25 actions, all remaining unknown slots are irrelevant and:

- 18 actions halt within **at most four counted steps**.
- 7 actions never halt, proved using full physical-tape finite-cycle or fresh-direction invariants.

The Lean theorem `mixed_decided B (4 ≤ B)` classifies **every** compatible completion. A second theorem `mixed_reached_branch` genuinely constructs a `Cover.branch` on the *visited* B/0 slot, with all 25 children receiving source-derived `Cover.leaf` proofs. This is a stronger coverage-tree integration test than a branch on an untouched table entry, though its small parent cylinder contains multiple halting slots and does **not** belong to the exactly-one-halt-normalized representation.

The parent covers precisely `25^6 = 244,140,625` complete canonical tables, split into `18×25^5=175,781,250` halters and `7×25^5=68,359,375` nonhalters. These **must not be added** to the earlier nonhalting union count without overlap analysis. This branch has passed local signature-matching source compilation but its final original-Frontier/LeafRules CI verification is pending; the local cycle lemma was declared as a matching mock during typechecking and is not evidence for the final source result.

## Historic unresolved-root overlap audit

The self-contained [`holdout_overlap.py`](holdout_overlap.py) reads the pinned repository resource `resources/BB6_holdouts_663_2026-10-16.txt` and strictly parses all 663 distinct six-state RLE codes. Exactly **zero** of the listed historical roots satisfies the two Boolean control-closure families or the particular transient and bounce examples. This provides an explicit negative check against misleading table-percentage claims. The audit does not imply the 663 roots remain the current live list, nor that the source list is complete or up to date. It was replayed successfully in the existing manual CI.

## Verification boundary

The complete **unmodified** Agent 8 `Frontier.lean` and new `DirectedDrift.lean` compiled in successful manual-only [CI 41503271213](https://github.com/FlareZ123/bb6/actions/runs/41503271213) using Lean 4.36.0-rc2. All three new theorem axiom audits report only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The existing [Agent 44 manual workflow](../../.github/workflows/agent44-p1-envelope-verify.yml) now builds the unchanged `Frontier` module before the new proof, alongside the previously source-checked power envelopes. Local signature-matching mock compilation was preliminary and is superseded by this full-source result.

No mathematical discovery about an actual BB(6) holdout is claimed. The practical advance is a more expressive source-checkable nonhalting decider leaf for future exhaustive search.
