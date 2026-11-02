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
