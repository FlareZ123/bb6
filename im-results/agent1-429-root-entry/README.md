# Exact blank-root entry and initial head-frontier development for #429

## Mathematical statement

For the explicit complete twelve-slot table `source429`, the blank A-root
executes exactly 35 successful primitive transitions and reaches the
configuration `j00Config`:

- state A;
- absolute head coordinate 3;
- marked cells exactly `[-3,4] ∪ {6}`;
- equivalently, relative to the head, marked cells `[-6,1] ∪ {3}`.

The final tape has the defining support pattern of J(0,0). `JRootEntry.lean`
records the complete table (including the genuine D/1 halt), the ordered
35 writes, the exact support theorem, and
`run source429 35 blank = some j00Config`.

## Root-history and gate-safety lemmas

The file defines a raw physical `runWithHeadMax` monitor. It includes the
initial and final configurations and updates the maximum at every successful
primitive step. The generic theorem `runWithHeadMax_projects` proves that a
successful monitored run projects to the repository's ordinary `run`
semantics, so the monitor changes no transition or halt convention.

The monitor also has a proved segment-composition law,
`runWithHeadMax_add`: the maximum over a concatenated run is the maximum
of the two segment maxima. `runWithHeadMax_two_of_rawSteps` gives its exact
two-transition specialization.

Three reusable lemmas now formalize the frontier mechanism:

1. `runWithHeadMax_tape_above`: every tape cell strictly to the right of a
   successful run's maximum head coordinate is unchanged from the input tape.
2. `runWithHeadMax_current_max_right_blank`: if the monitored endpoint is
   itself at the reported maximum and the input tape has a blank right tail
   beginning no farther right than that maximum, then the endpoint's right
   neighbor is blank.
3. `c0GateAfterTwo_frontier`: the C/0-to-D/0 two-step gate writes the new
   rightmost mark one cell beyond its input head whenever the old tape had a
   right blank tail.

The local gate lemma `source429_c0_gate_two_steps` proves that a C/0
configuration with a blank right neighbor executes C/0 then D/0, writing a
new 1 at the next cell and returning left in E/1. The companion
`c0GateAfterTwo_frontier` proves that this new cell is the rightmost mark
when the input already had a blank right tail. This packages the exact
mechanism by which a C/0 event at the current global head frontier is safe
and advances the frontier by one.

## Concrete blank-root prefix

The explicit-table raw monitor proves:

- After 35 steps, the endpoint head is 3, the maximum visited head is 6,
  and the rightmost mark is 6.
- The next 110-step continuation from that endpoint has head maximum 12,
  endpoint head -3, a mark at 12, and no marks to its right.
- After 271 total root steps, the endpoint head is 11, the maximum visited
  head is 12, and the rightmost mark is still 12.
- At the 275-step endpoint, the machine is in C/0 at head 15, which is the
  current global head maximum. The generic monitor lemma proves cell 16
  blank; it is not accepted by direct table lookup alone.
- The C/0-to-D/0 continuation then writes cell 16. After 277 total steps,
  the endpoint is E/1 at head 15, the global maximum is 16, cell 16 is
  marked, and every cell to its right is blank. The 277-step monitor result
  is now derived compositionally from the 275-step prefix and the generic
  two-step gate monitor via `runWithHeadMax_add`; the endpoint is proved
  equal to the gate's exact post-state.

Thus the root-connected finite prefix exhibits the invariant pattern
`historicalHeadMaximum = currentRightmostMarkedCell` at its certified
frontier checkpoints (6, 12, then 16). This is a finite root-history result,
not an all-time invariant.

## Extended source-connected J-chart prefix (new candidate)

`RootToJunc.lean` supplies the 145-step blank-root checkpoint
J(0,12), at absolute head (-3), with head maximum 12 and a complete
physical `Represents` proof. The new `RootJunctionChain.lean` adds an
exact 1463-step source-zipper monitor

```lean
runWithMax 1463 (junc 0 0 12) =
  some (junc 21 0 11, 15, 29)
```

and lifts it to the complete physical tape. The physical segment begins at
head (-3), ends at head 12, and every primitive prefix has head at most
26. Composed with the 145-step root checkpoint, this gives the candidate
blank-root statement at step 1608: J(21,11), head 12, rightmost mark 26,
and exact historical head maximum 26.

The same file composes the corrected low43 physical branch from J(21,11)
to J(11,62). It gives a 1559-step segment, net head displacement (-41),
and local prefix maximum (+24). After translating the segment by the
root head coordinate 12, the resulting candidate blank-root checkpoint is
step 3167, J(11,62), head (-29), rightmost mark 36, and exact historical
head maximum 36. The proof reconstructs a raw `runWithHeadMax` monitor
from raw-run success and all-prefix bounds; the lower bound on the maximum
comes from the newly marked rightmost endpoint cell, while the upper bound
comes from the physical prefix monitor.



The same chain is now extended another 2457 steps. A concrete high-three
branch J(11,62) -> J(25,37) takes 621 steps with displacement +25 and
maximum +25. The exact (v=18,n=2) low-odd return J(25,37) -> J(10,74)
takes 1836 steps with displacement (-34) and full-prefix maximum +43.
Composing these monitors gives J(11,62) -> J(10,74) in 2457 steps,
displacement (-9), maximum +68. The physical lift in
`Low43RootPhysical.lean` retains the all-prefix bound. The new
`root_after_5624_junc10_frontier` theorem in `RootJunctionChain.lean`
therefore claims the blank root reaches J(10,74) at step 5624, head -38,
rightmost mark 39, and exact historical head maximum 39.

The 1836-step low-odd maximum is a concrete `by decide` monitor, not a
general low-odd max theorem. The next simulated state J(49,2) is reached
from J(10,74) by the existing high-three ladder, and its concrete
r=96 return to J(11,98) is separately formalized as a prepared-input
physical theorem. The full root composition through J(49,2) and J(11,98)
is still pending.



The high-three ladder from J(10,74) to J(49,2) is now monitored in two
separate exact source chunks: J(10,74) -> J(23,51) in 527 steps
(displacement/max +23), then J(23,51) -> J(49,2) in 2373 steps
(displacement/max +49). Their composition is 2900 steps, displacement
+72, maximum +72. Composing the concrete low-even r=96 return
J(49,2) -> J(11,98) (719 steps, displacement -89, maximum +12)
gives a 3619-step J(10,74) -> J(11,98) physical segment with
displacement -17 and maximum +84. The new
`root_after_9243_junc11_98_frontier` theorem claims the blank root reaches
J(11,98) at step 9243, head -55, rightmost mark 46, and exact historical
head maximum 46. The 2900-step monitor is composed from two smaller
`by decide` certificates; the monolithic 2900-step decision exceeded
the local recursion/compute budget.

These declarations are kept in `im-results/` pending the full dependency
workflow. The finite zipper equations were reproduced locally with Lean
4.36.0-rc2 and `by decide`, but the composed physical file has not yet
passed repository CI. The manual workflow
`.github/workflows/agent1-429-root-junction-chain.yml` builds the root,
high-zero, high-three, low43, and physical dependencies, then checks the
new root-after-1608 and root-after-3167 axiom reports and rejects
`sorryAx`. It has not yet been dispatched. Until that workflow succeeds,
treat this as a source-level proof candidate rather than CI-certified
evidence.

## Evidence and source boundary

The 35-step and finite-prefix monitor equations are kernel computations.
The generic monitor projection, head-bound, tape-above, and gate-safety
lemmas are Lean-proved. The exact finite-support tape theorem is proved by
case splitting over the write support and integer arithmetic. A local Lean
4.36.0-rc2 preflight against a source-equivalent copy of the relevant
`BB6Coverage` operational definitions (`Config`, `run`, `rawStep`,
and `applyMove`) compiles the declarations; the axiom reports contain only
standard axioms (`propext`, `Classical.choice`, `Quot.sound` as needed),
with no `sorryAx`.

The explicit table bridge is now present in [SourceBridge.lean](SourceBridge.lean).
Its kernel proof establishes pointwise equality
`source429 = BB429PhysicalFrontier.target429` by exhausting all twelve
state-symbol slots. It then transfers both the 35-step blank-root entry and
the 277-step monitored frontier certificate to the repository's canonical
physical #429 table. The generic monitored-record C/0 frontier theorem is
also transferred to `target429`.

The bridge now imports the canonical `JPhysicalPrefix` module and proves
`rootTape_matches_physical_j00`: the 35-step endpoint tape is exactly
`BB429JPhysical.jTape 0 0`, translated by the absolute head coordinate 3.
Thus the root entry is not merely shape-compatible with a locally defined
predicate; it is identified with the physical J(0,0) tape used by the
source-connected J/Junc developments.

The bridge has been locally preflighted against a minimal replica of the
repository's `PartialMachine`, `refine`, and eleven-entry completion
definitions. This confirms the proof script and table equality, but is not a
substitute for compiling against the actual imported physical module. The
manual workflow `.github/workflows/agent1-429-physical-frontier.yml` now
compiles `JRootEntry.lean` and `SourceBridge.lean` after the actual
`BB429PhysicalFrontier.olean` is built, and checks that the source-identity
and 277-step frontier theorems appear in the axiom audit. That updated
workflow has not yet been dispatched. The smaller
`.github/workflows/agent1-429-root-entry.yml` remains a standalone
operational-definition preflight.

## Why the entry matters

The exact root base and the generic gate-safety lemma isolate a concrete
route to the global C/0 argument: maintain
`historicalHeadMaximum ≤ currentRightmostMarkedCell` across every J/Junc
macro; show each exceptional C/0 gate occurs at or beyond the old frontier;
then its right neighbor is blank, and the C/0-to-D/0 pair advances the
rightmost mark to cover the new maximum.

The existing ordinary and exceptional macro certificates provide many of
the local pieces. The missing theorem is their source-connected, all-time
composition along the actual blank-root orbit.

## Remaining open problem

This work does not prove that the subsequent J/Junc orbit stays in a safe
chart, that every later C/0 event is at the global frontier, or that #429
never halts. The root is now connected through a candidate source-verified finite chain to J(11,62), but the all-time physical frontier/history invariant remains open. The next root-specific transitions (including the low-odd and low-even returns) still need their complete prefix maxima composed with the blank-root history, and the general J/Junc chart must be closed across every regular and exceptional transition.

Keep this candidate in `im-results/`. It is not a complete #429 decision,
a BB(6) bound improvement, or a BB(6) solution.
