# Enumerate62 source expansion adapter

## Status

The Lean adapter in `Enumerate62Adapter.lean` passes the focused
`source-queue-adapter` target in `.github/workflows/agent13-coverage.yml`
(run **45399254432**, commit `c80dd8f5c7a0a9a75f7717707f312edcc1ce22fd`).
The workflow rejects `sorryAx` and `native_decide`; that gate passed.
Its printed axiom dependencies are inherited standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`), not proof placeholders.

The separate Coq theorem `Agent5Enumerate62DeciderSound.v` is still under
focused CI validation. It is intended to package the soundness of the actual
upstream `TNF_Node.decider`; it is not yet accepted.

## Source correspondence

The reference is `ccz181078/busycoq`, pinned at
`33209bc7dc282b38c8cd6be507bfc551fea56108`, file
`verify/Enumerate62.v`.

The Lean adapter uses the same finite table encoding:

- Coq states A..F correspond to `Fin 6` values 0..5.
- S0/S1 correspond to `false/true`.
- L/R correspond to `false/true`.
- A table slot is `(state, symbol)`.
- The root table is exactly
  `TM_from_str "1RB---_------_------_------_------_------"`.

Crucially, a source `None` is an *unexpanded transition slot*. The adapter
maps it to outer `none` in `PartialMachine`; a known halting transition
would instead be `some none`. An assigned ordinary move maps to
`some (some move)`.

## Proven adapter facts

- `sourceRoot_action` and `sourceRoot_wf`: the node0 root action and its
  exact 11-slot hole list are represented correctly.
- `sourceChild_partial`: assigning one source slot is exactly the local
  `refine` operation.
- `sourceChild_holes_length`: the source hole-list length decreases by one
  when an undefined slot is assigned.
- `sourceChild_support` and `sourceReachable_wf`: reachable source children
  preserve the state-support invariant needed by the weighted TNF argument.
- `sourceChoices_mem_iff` and `sourceExpand_child_iff`: the source expansion
  enumerates all four write/direction choices for every destination
  (q\leq cut). This is the union of the old labels (q<cut) and the one
  least-fresh label (q=cut), when it exists.
- `sourceExpand'_last_hole_empty`: the source `expand'` one-hole branch
  returns no ordinary children.
- `source_last_hole_cover`: the one-hole branch is semantically covered:
  the exact hole list proves every other table slot is assigned, so
  `last_hole_sound` applies once the first-hole blank run and weighted halt
  delay bound are supplied.
- `source_expand_cover`: for a non-last first hole, the local
  `first_hole_tnf_cover` theorem applies to exactly the source expansion
  children, with one obligation for each old-label branch and each
  least-fresh-label branch.

The hole list is a ghost representation used to make the source's
`num_undef_trans` count exact. It is maintained from the root by erasing the
assigned slot. The adapter's `SourceWF` is deliberately not claimed to be the
entire upstream Coq `TNF_Node.WF`: it captures exact holes, the fresh-label
bound, and state support. The source's unused-state permutation condition is
handled locally by the weighted TNF renaming argument, but a queue-wide
compatibility quotient still needs to be connected explicitly.

## Remaining proof boundary

This is not a BB(6) upper-bound certificate and does not yet prove that the
upstream queue's final active/holdout frontier covers every six-state machine.
The non-last theorem is conditional on child weighted certificates; the
last-hole theorem is conditional on the first-hole run and weighted delay
bound. The separate Coq decider theorem is being checked to establish
`Halt h -> halts_at ... h` and `NonHalt -> never halts` for the actual source
classifier.

The next high-value integration steps are:

1. Connect the Coq `decider` branch theorem to the Lean first-hole
   `knownRun` semantics (including the stream-tape / integer-tape simulation).
2. Instantiate the queue coverage contract with source children and a
   compatibility relation that accounts for fresh-state renaming.
3. Connect the actual `SearchQueue_upds` / `holdout_i` chunks and their
   terminal certificates to that invariant.

Do not report this adapter alone as a proof of the global upper bound.
