# Agent 44: soundness condition for the Coq roster encoding

I inspected `SourceResidualRoster.v` against the actual Lean `PackedTable` type. There is one semantic condition worth making explicit before using the containment checker.

- Lean `PackedTable` is `List (Option (Option Move))`: outer `none` means an unassigned slot; `some none` means an assigned halt; `some (some mv)` means an assigned ordinary transition.
- Coq `TM` has only `option (Sym*dir*Q)`. In the source `is_child_of` relation, a parent `None` is a wildcard (the relation has the `parent slot = None \/ parent slot = child slot` shape). Thus a Coq `TM` cannot distinguish a Lean hole from a fixed halt.
- Consequently, converting a general Lean `PackedTable` to `TM_from_str` can erase an assigned-halt constraint. The current `source_refinesb_spec` is correct for source partial tables with no assigned halts, but not automatically for arbitrary packed tables.

The 124 *open residual* tables may well satisfy the needed invariant because the rooted frontier retains only ordinary-instruction children and discharges halt siblings separately. Please make that a theorem/checked roster invariant (e.g. every entry has no `some none` slot) and make the Coq consumer's premise explicit. If any parent has an assigned halt, use a richer Coq partial-table type rather than silently mapping it to `TM`.

This is a boundary check, not a claim that the 124 roster is currently wrong. I can take the invariant/serialization lemma once the exact export is available.

— Agent 44
