# Agent 13: raw six-state coverage and sparse-trace proof interface

**Status: kernel-verified foundational intermediate theorem, not a BB(6) decision or a new bound.** This module provides two explicit, all-machine proof interfaces missing from the local BB(6) completeness chain. It is deliberately in `im-results/`, not `results/`.

## Exact semantics and canonicalization

The Lean 4.36.0-rc2 module `BB6Coverage.lean` defines a six-working-state, two-symbol, bi-infinite-tape Turing machine. The initial working state is state 0 (A), the initial head position is 0, and the tape is all false (0). Attempting a halt transition counts as **one step**. A raw transition has 2 write values, 2 directions, and 7 destinations (6 working states plus halt), hence 28 possible entries. When a halt destination is chosen, the write and direction fields do not influence subsequent behavior or the first halting time.

`encodeInstruction` and `decodeInstruction` provide a **proved bijection** between the 25 canonical options (one halt plus 24 ordinary transitions) and `Fin 25`. The proofs `decode_encode_instruction` and `encode_decode_instruction` are source-level Lean theorems using `decide`, not an external enumeration oracle.

The maps `encodeMachine : RawMachine → CodeMachine` and `liftMachine : CodeMachine → RawMachine` establish:

- `decode_encode_machine`: every raw table has an exactly matching canonical table;
- `encode_liftMachine`: every canonical table arises from a genuine raw table;
- `normalized_haltsAt_iff_code`: **all exact blank-start halting times** agree between the raw table and its canonical code;
- `flatten_unflatten` and `unflatten_flatten`: a code table's six rows and two symbol columns are bijective with `Fin 12 → Fin 25`;
- `universal_bound_iff`: an all-machine halting-time bound is true in raw semantics exactly when it holds for every canonical code;
- `code_upper_bound_and_raw_witness`: a genuine B-step raw halting witness plus a universal canonical-code bound imply `ExactBB6 B`.

The arithmetic checks `raw_choice_count` and `simple_choice_count` establish `28^12 = 232218265089212416` and `25^12 = 59604644775390625`. These are *full transition-table counts*, **not** the number of sparse TNF representatives or unresolved holdouts.

## Sparse enumeration safety

`table_trace_preserves_run` and `table_trace_preserves_halting_time` show that if two canonical tables agree on the state/symbol entries actually queried by the first machine during its first `n` attempted steps, then their blank-start configurations are identical through step `n`, and they halt at precisely the same time `n` (if at all). This lemma applies even when entries *not* visited along the trace differ arbitrarily.

This is a certified foundational rule for a future sparse-enumeration checker: one can leave transitions unfilled while preserving a known finite trace and a halting certificate. It does **not** prove that a particular sparse enumeration is complete, nor validate any previous six-state decider output, normal-form search tree, externally listed holdout inventory, or maximal runtime.

## Reproduction

Stored source: `BB6Coverage.lean.xz.b64` (xz-compressed and base64 encoded); `unpack.py` reconstructs `BB6Coverage.lean` with a checksum check and an atomic, exclusive-lock write. Original uncompressed SHA-256:

`fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd`

Run `python unpack.py` in this directory, then compile `BB6Coverage.lean` with Lean 4.36.0-rc2 (only `import Std` is required). Local Lean compilation succeeded; `#print axioms` gives **only `propext` and `Quot.sound`** (or their subset) for every listed theorem, no `sorryAx`, `native_decide`, new axiom, or external lean library.

External context: [bbchallenge sparse enumeration method](https://bbchallenge.org/method) and [TNF reduction rules](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form). These are methodological references, not proofs that our raw-table vocabulary already matches every edge in an external finite enumeration.

## Missing global implications

1. Establish a mechanically verified reduction from all `Fin 12 → Fin 25` tables into an actual *complete* six-state TNF/search tree, including reflection, state renaming, pruning, and branch termination.
2. Verify each terminal branch's nonhalting certificate or certified halting runtime, with no stale or unverified holdout assertions.
3. Exhibit a raw halter at the greatest verified runtime and derive a globally certified upper bound matching that value.

The 2026-10-16 list of 663 rooted representative machines and the local 435-unrooted-table grouping are triage inventories. Neither is a proof of step 1. The module's universal theorems avoid assuming that inventory is exhaustive.


## Source-certified sparse search and nonhalting leaves

The separate modules `SparseCoverage.lean` and `LassoCoverage.lean` import the first source file and close two additional proof links that support a future verified TNF search-tree generator.

**Partial-machine branch coverage:** A `PartialMachine` has twelve slots of type `Option SimpleInstruction`. Here `none` means *unassigned*, and `some none` means an intentionally assigned **halting** instruction. This distinction prevents accidental conflation of an open TNF search-tree branch with a halting machine. The all-natural theorem `split_covers_every_code` establishes that for any canonical full table extending a partial table and any unassigned slot, the unique child obtained by filling that slot with the full table's actual choice still covers that full table. `child_extension_is_parent` proves each child remains inside its parent space. These are the exact local branch-completeness conditions for a future depth-first finite search.

**Trace and certified leaf correctness:** `all_extensions_agree_on_prefix` proves that when the entries queried by one finite prefix are all assigned, *every* full completion has the identical prefix. `halting_leaf_sound` certifies the exact halting time for every completion when one such prefix halts. `repeated_configuration_nonhalt` proves a general deterministic infinite-run theorem: if one entire configuration (including its infinite tape) recurs at steps `i<j`, no future run step can halt. Finally, `sparse_lasso_leaf_nonhalts` lifts such a lasso to every extension of a partial table whose prefix was fully assigned. This is a mathematically complete finite-configuration cycler decider rule, conditional on an authentic equality of infinite configurations. No actual new holdout has been assigned a loop certificate.

Original source hashes: `SparseCoverage.lean` SHA-256 `c2271613c1c9676e1ef1cd92ed0ad07647e1e0187a11614a5d9e643c01cbc809`; `LassoCoverage.lean` SHA-256 `8544a335fb62a34329dc0c07edeeb5a948a3afb7a314b95f7d1f712cfb57c730`. All three compressed source blobs are reconstructed by the same locked/atomic `unpack.py`. Compile in order `BB6Coverage`, `SparseCoverage`, then `LassoCoverage`, with `LEAN_PATH=.`. Local Lean 4.36.0-rc2 checked all three with only standard axioms and no sorry.

**Remaining coverage gap:** These lemmas prove that a correctly built search tree cannot lose a table when it branches on an unassigned slot, and that individual certified halt/cycler leaves are valid for all completions. They do not prove a particular recursive search algorithm visits every reachable pending branch, that other more powerful deciders are sound, or that all six-state machines obtain a certified outcome. The source-to-sparse-enumerator completeness theorem and the universal runtime comparison remain open.


## Complete proof-tree composition, translated cyclers, executable tapes

The source chain now extends to **seven** modules, all compiled locally under Lean 4.36.0-rc2 with only standard axioms. A manually dispatched full-chain CI workflow pins the toolchain and checks the unpacked source hashes.

### Translation-invariant cyclers

`ShiftCoverage.lean` introduces `shiftConfig d c`, which shifts both the head and every cell of the entire infinite tape by an arbitrary integer displacement. `tick_shift` proves exact source-step translation covariance, and `shifted_configuration_nonhalt` proves that if a real run has configurations `c` at time `i` and `shiftConfig d c` at time `j>i`, **every subsequent step is defined**. It therefore extends the lasso certificate to drift/translated-cycle phenomena. `sparse_shift_cycler_leaf_nonhalts` lifts this to every full table completion of a correctly assigned observed prefix. Neither lemma assumes that two configurations with matching local tape *windows* are equal on the full tape. Infinite tape equality or a verified finite-support equivalent is mandatory.

### A falsifiable end-to-end proof contract

`TreeCoverage.lean` defines `CoverTree B p : Type`, an inductive, **proof-carrying** search tree. Its constructors are a certified halter leaf bounded by B, exact full-configuration cycler leaf, translated cycler leaf, and **25-way exhaustive split** on an explicitly unassigned state/symbol entry. Source-level theorem `coverTree_sound` proves that every completion of the partial root has halting time at most B; `rooted_coverage_upper` lifts a complete tree from the *entirely unassigned* root to **every raw six-state machine** under the stated semantics. The final Lean theorem

```lean
full_bb6_from_coverage_and_witness (B : Nat)
  (tree : CoverTree B unassigned)
  (witness : ∃ m : RawMachine, HaltsAt (tickRaw m) B) : ExactBB6 B
```

is the precise **conditional** goal. No `CoverTree B unassigned` exists in the repository and no missing BB(6) witness is asserted. The type requires each gap to be closed with checked proof terms; recursively branching without certified leaves cannot forge a coverage proof.

### Executable finite-support physical tape

`FiniteTapeCoverage.lean` implements `FinConfig` as a working state, integer head, and finite list of positions containing symbol 1. The tape is zero everywhere else; the list may have any order. `finiteTick_correct` proves that each computable finite-tape transition agrees with `tick` over the **whole bi-infinite tape**, and `finiteRun_correct` proves this for arbitrarily long prefixes. `finite_run_halts_at` turns verified bounded finite simulation into an original infinite-tape halting certificate. `sameFinConfig` compares tapes using finitely many membership checks rather than external semantic equality. `finite_cycle_nonhalt` turns an executable finite-state recurrence into an all-time source-level nonhalting proof.

`FiniteTapeShift.lean` further proves `shiftFinite_correct`, equating finite list translation with full infinite tape translation, and `finite_shift_cycle_nonhalt` for concrete executable shift-recurrence certificates. `assignedFinite_sound` transports finite prefix assignment into the original sparse trace predicate. Finally, `finite_shift_tree_leaf` constructs an actual inhabitant of `CoverTree B p` from a verified finite shift-cycle witness, allowing a certifying search engine to build sound proof objects by composing finite computations and 25-way branches.

**Source hashes (uncompressed SHA-256):**

- `ShiftCoverage.lean`: `3ea7b0bbac9b2ca575b34c362b478e52c335d390113b2934a4c73b0e2f309c3e`.
- `TreeCoverage.lean`: `c5d2858599d0ad1beaa993c106f35bb0c5152cb22659a11575450a344731eeab`.
- `FiniteTapeCoverage.lean`: `7ce8ab8c411038a0ca0f9ff568c23529dae4b7c514689dd2b14eb9c44bd17000`.
- `FiniteTapeShift.lean`: `23bed37b7c46bc7d46714700605ca9309656a99558a8565b2b15c877fd194579`.

The `unpack.py` reconstructs all seven source files and refuses any source hash mismatch before compiling. Each source uses the unchanged previous theorem imports and source integrity is audited by manual CI.

### Remaining hard research, precisely stated

1. **Construct a real global `CoverTree B unassigned`** or extend its sound leaf constructors with more general formally verified nonhalting deciders. The current proof tree is a trusted proof object interface, not an instantiated exhaustive search. Enumerating 25^12 tables directly would be prohibitively large.
2. Mechanically verify normal-form reductions (including first-state renaming, reflections, write-symbol constraints, initial state, and initial blank) against the exact standard BBChallenge/DeepMind convention. Our raw semantics is mathematically explicit; there is not yet a kernel-certified import-level equivalence with an externally enumerated six-state machine vocabulary.
3. Connect all external decider outputs, including machines removed *before* the dated 663-root holdout list, to trusted terminal proof objects. Distinguish proven halting times, proven all-time nonhalting, and unresolved roots.
4. Establish and verify the maximum attainable raw step count. The present project still lacks a universal solved-BB(6) bound.

**Strict evidence classification:** these are source-level, verified general-purpose *foundational* results with a clear missing-premise boundary. They are not newly resolved BB(6) machines, a complete enumeration, or publishable original Busy Beaver frontier results.
