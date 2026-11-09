# #429 low-J returns: source-certified deficit-three physical theorem and wider residue conjectures

**Scope and research state (9 November 2026).** The original six-state table is
`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`.
For the canonical prepared infinite tape `J(u,w)`, previously established
source-certified [high and fatal branches](../agent18-429-junc-canonical/README.md)
cover `w+1≥2u`. This dossier addresses `r=2u-w≥2` with exact source
dynamics and full-tape geometry. The remaining all-time *authentic blank-origin*
question is whether the genuine root orbit can reach any fatal
`w+1=2u` J section or its original B/001 equivalent. The present
prepared-tape statements do not decide #429 or BB(6).

## Deficit-three: full original-machine theorem established

The source-stage theorem `BB429Low3Delta.stage3_to_junc_delta`
in [Low3Delta.lean](Low3Delta.lean) establishes an all-natural exact
signed symbolic return using only the original source table and a fast,
independently verifiable dependency path:
```lean
stage3 v = z 0 (ones (4*v+4) ++ (true::false::ones 6)) true [false,true]
runWithDelta (12*v+48) (stage3 v) =
  some (junc 0 0 (4*v+10), -((4*v+8 : Nat) : Int))
```
The [Low3Physical.lean](Low3Physical.lean) theorem connects that
signed source stage to the original six-state interpreter, using
`BB6Bubble.multi_bubble_prefix` after `v+1` bubbles,
`BB429DeltaPhysicalBridge.source_runWithDelta_rep`, and an
entire-infinite-tape identification. Its exact kernel-checked statement is:
```lean
theorem BB429Low3Physical.low3_raw_head (v : Nat) :
  ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429
    (4*v*v+22*v+54)
    {state:=BB6Bubble.A,head:=0,
     tape:=BB429JPhysical.jTape (v+2) (2*v+1)} = some c' ∧
    BB429PhysicalBridge.Represents
      (BB429FinishScanEDelta.junc 0 0 (4*v+10)) c' ∧
    c'.head = -((2*v+6 : Nat) : Int)
```
In the usual `u=v+2` coordinates this proves the exact full-tape
transition `J(u,2u-3) → J(0,4u+2)`, after
`4u²+6u+26` successful primitive moves, with the final physical
head at `−2u−2`. The weaker `low3_raw` theorem is a corollary.

**Exact source alignment of the new proof.** The first `v+1` successful
bubbles execute `4(v+1)²+2(v+1)` instructions and place the physical
head at `2v+2`, without changing any cell beyond filling the
negative-even holes at `−2,−4,…,−2(v+1)`. Every intermediate tape cell
is characterized by
```text
negFill (jTape (v+2) (2*v+1)) (v+1) x = true
iff ((-2v-10 ≤ x ≤ 2v+2 and x ≠ -2v-4) or x = 2v+4).
```
This gives precisely `stage3 v`, including the two infinite blank
tails. The remaining `12v+48` source moves yield total
`4v²+22v+54` primitive moves and net displacement `−4v−8`;
composing with the bubble-head position `2v+2` gives the exact final
position `−2v−6`.

**Original-source verification passed:** [manual CI run
42605756502](https://github.com/FlareZ123/bb6/actions/runs/42605756502)
compiled the unmodified repository's original definitions, the new
`Low3Delta` source proof, and the entire `Low3Physical` theorem
at Lean 4.36.0-rc2. Its axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`, and the
workflow rejects `sorryAx`. An earlier manual attempt was
runner-shutdown-interrupted on a redundant expensive upstream dependency;
the final source proof removed that dependency and passed.

The adjacent `r=2` original-table physical return already has the
Agent 6 [Low2Physical.lean](../agent6-429-low2/Low2Physical.lean)
source proof candidate, likewise subject to its separate original-import
CI status. The `r=2` prepared section occurs in the genuine accelerated
root trajectory, making these low branches more than a synthetic parameter
curiosity. A formal all-time root/halting decision remains missing.

## Remaining low-J residue-class experiments

The original [explore_low_j.py](explore_low_j.py) uses the entire
bi-infinite-support finite set of one-cells and compares the predicted
full endpoint, state and head. It found **554 matching cases** across
`2≤r≤34` within its stated parameter bounds. The following formulas are **finite computational conjectures**
outside the explicitly source-certified `r=3` row and other separately
proved branches.

| Offset `r=2u-w` | Primitive steps `T` | Target `(U,W)` | Head | Restriction |
| --- | --- | --- | --- | --- |
| `4k+2` | `4u²+(14−16k)u+16k²−10k+61` | `(0,4u+8−4k)` | `−2u−3` | `k≥0` |
| `4k` | `4u²+(22−16k)u+16k²−26k+261` | `(11,4u−4k−2)` | `9−2u` | `k≥1` |
| `4k+1` | `4u²+(14−16k)u+16k²−6k+60` | `(2k+4,4u−8k−2)` | `−2u+4k+4` | `k≥1` |
| `4k+3` | `4u²+(6−16k)u+16k²+26k+146` | `(2k+9,4u−8k−10)` | `−2u+4k+10` | `k≥1` |
| `3` | `4u²+6u+26` | `(0,4u+2)` | `−2u−2` | `u≥2`; source-certified theorem |

The target `W` and start `w` must be nonnegative, with additional
restrictions where specified. For example, `r=7,u=4` has negative
predicted target `W`; a different return was observed at step 563.
The five formulas cannot be extrapolated to such boundary inputs.

## Mathematical next step

The `r=3` physical return and signed head offset are now established.
The next decisive step is to connect this exact transition to authenticated
Cryptids blank-root J sections and their accumulated translation offsets,
then constrain all possible authentic feeder paths into a fatal boundary.
The decisive unresolved quantifier is the infinite authentic orbit's
avoidance or occurrence of the fatal boundary. Further congruence
sieves or finite sample increases are lower priority unless they
directly close that root reachability problem. The existing
[halting-gate dossier](../agent6-harmonic429/README.md) and
[physical B/001 bridge](../agent32-429-raw-parent/README.md) are
relevant downstream starting points.
