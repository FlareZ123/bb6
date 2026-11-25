# Cross-route closure of the q_i 2800 held leaf

**Status:** intermediate proof integration. This closes one exact source-queue leaf and proves how it sits inside the independent first-one root frontier. It does **not** close the parent residual or establish the global BB(6) upper bound.

## Exact source checkpoint

Agent 5's recovered source checkpoint records the held node at `q_i 2800 100` as:

```text
1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---
```

Its metadata is:

- 11 assigned transitions and one hole, at `F1`;
- six introduced states (`fresh = 6`);
- source chunk offset 2800, size 100.

The committed exporter `check-q0-export.cjs` independently counts `---` holes and computes the fresh-state cut as the initial consecutive set of states reached from the initial state A. The displayed table reaches all six states A–F, so its cut is 6. The source checkpoint is one of the recovered active/held queue outputs; do not mistake this one held leaf for a drained queue.

## Exact root-frontier address

In `im-results/agent50-weighted-tnf-pilot/root-frontier.json`, residual index 10 has address `B0=1LC` and table:

```text
1RB---_1LC---_------_------_------_------
```

This is a depth-one residual of the authentic first-one root `A0=1RB`. The source held table fixes the same A0 and B0 entries and nine additional slots. The Coq bridge `Agent13CrossRouteHeldLeaf.v` proves the exact `source_refinesb` relation twice and composes it with `child_trans`, so the held source node is a child of the authentic first-one root through that precise residual.

**Encoding invariant.** The source Coq `TM` representation uses `None` both for an unassigned slot and for a halting instruction, while `source_refinesb` treats a parent `None` as a wildcard. This pilot is safe under that interface because neither the root residual nor the held table contains an assigned halt: all fixed entries are ordinary moves, and F1 is genuinely unassigned. The Lean module proves `held_no_assigned_halts` and `root_no_assigned_halts`. The source safety theorem still quantifies over every extension at F1, including the halting choice; it does not assume that F1 is filled with a particular move.

## Independent FARv3 nonhalting certificate

`im-results/agent5-weighted-tnf-queue/Agent5RecoveredHeld.v` rechecks the existing FARv3 `nonhalt208` certificate for the reflected table:

```text
1LB0LD_1RC1RB_0RE1LA_0RC0LA_1RF1RD_1LD---
```

It invokes `RWL_mod_FAR 20000 10000 3 3200 2 4 2 0`, transfers nonhalting through the source's left/right `flip` symmetry and an identity state permutation, and proves `recovered_held_2800_nonhalt`. The final theorem `recovered_held_2800_safe bound` applies `source_nonhalt_cylinder`, whose definition quantifies over every extension of the partial table. Thus this is a complete one-hole cylinder proof, not a finite-run observation.

Because the transferred statement is **nonhalting**, it is stronger than any finite weighted bound. A finite blank-delay offset or a final-query counting convention cannot create a halting completion that the nonhalting theorem excludes. The remaining F1 query is universally quantified over by `source_table_safe`; it is not silently fixed to one chosen transition.

The prior CI run 45536703560 compiled `Agent5RecoveredHeld.v` and printed its assumptions before failing later in the unrelated `Agent47SourceTree.v` step (line 67). This dossier adds an isolated original-source target, `enumerate62-held-farv3-pilot`, so the table bridge and held proof can be compiled without that unrelated tree checker. Its result is pending until that target succeeds.

## Exact complement preservation

`CrossRouteHeldLeaf.lean` models the twelve transition slots with a separate `none` for an unassigned slot and proves:

- the parent residual has 10 holes;
- the held leaf has exactly one hole, F1;
- the leaf introduces nine additional fixed slots;
- the source fresh-state cut is 6;
- every completion of the parent either extends the held leaf, or disagrees with it at one of those nine new slots.

The last theorem is the key non-loss statement: consuming the FARv3 leaf removes the **whole one-hole obligation**, while every completion outside it remains in an explicitly identified sibling branch. The parent B0=1LC residual is not itself closed.

Local Lean 4.36.0-rc2 compilation succeeded. Its axiom reports are limited to standard `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is present. The Coq FARv3 transfer reports `FunctionalExtensionality.functional_extensionality_dep` among its assumptions, inherited from the existing permutation/halting transport. That dependency is disclosed rather than hidden.

## Direct relationship to the 109 mixed-bound roster

The parent residual `B0=1LC` is raw residual index 10 (canonical index 6) in `canonical-121.json`. It survives the 15 whole-cylinder exclusions used by `Combined109Roster.lean`: the three `FiveHoleRoster` entries raw66/70/80 and the twelve `AllTwelveRoster` entries raw86/87/88/91/92/93/97/98/100/101/102/104. It is therefore one of the **109 retained obligations**, not an unrelated branch.

`Root109Membership.lean` formalizes that fact against the actual `BB6.Agent47Combined109.reducedRoster`: it proves the B0=1LC parent is not among the fifteen covered tables and is an exact member of the 109-entry list. It also translates the standalone twelve-slot table encoding into the roster's `BB6Coverage.PartialMachine` representation, proves the parent tables are identical, and proves the q_i 2800 held table is a strict refinement of that exact 109 parent.

The 109 roster count remains 109 until the consumer replaces this parent by the certified leaf plus its explicit complement. The `held_leaf_partition` theorem supplies the complement-preservation argument, but `Combined109Roster.reducedRoster` itself is not modified here. Thus this is a genuine closure of one subcylinder inside one of the 109 obligations, not yet a reduction of the roster count or a complete safety proof for the parent.

No claim is made here about exhaustion of all 129 source chunks, closure of the 207 root-frontier residuals, or the exact value of BB(6).
