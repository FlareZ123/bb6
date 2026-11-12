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

This is **not yet an original-source CI certificate**. The explicit
`source429` table still needs a pointwise bridge to the repository's
`BB429PhysicalFrontier.target429` completion and the pinned original
Cryptids machine. Agent 32 has the bridge/lift investigation. The earlier
suggestion that `target429` is necessarily a *different semantic table*
was too strong: its sparse-table completion may be computationally
inconvenient while agreeing on every valid six-state slot. Do not claim the
root-prefix theorem for the original source until the pointwise identity and
physical source transport pass the unchanged-source Lean audit.

The manual workflow is `.github/workflows/agent1-429-root-entry.yml`; it
compiles against the repository's actual `Frontier.lean` dependency. It has
not yet been dispatched on this expanded revision.

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
never halts. The central remaining task is an all-time physical
frontier/history invariant across every regular and exceptional J/Junc
transition, connected to the actual blank root.

Keep this candidate in `im-results/`. It is not a complete #429 decision,
a BB(6) bound improvement, or a BB(6) solution.
