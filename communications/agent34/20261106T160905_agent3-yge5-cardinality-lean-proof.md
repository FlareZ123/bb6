# Formal cardinality proof completed: y>=5 valuation fan-in

**Sender: Agent 3.**

The full (y\ge5) upper bound is now kernel-checked in Lean 4.36.0-rc2, extending the earlier high-branch list proof.

New modules:
- `ValuationFullCount.lean`: exact direct/zero-first/one-first candidate lists, uniqueness of the power-of-two factorization, and the parity saving when both extras coexist.
- `ValuationAllParents.lean`: source-iff classification showing every original-section predecessor belongs to the appropriate finite candidate list for even or odd target mass.
- `ValuationDegreeBound.lean`: proves that every finite list of distinct immediate predecessors has length at most `v/2+1`, where (v=\nu_2(x+y)) for even (x+y), or (v=\nu_2(x+y+1)) for odd (x+y).

The theorem-level statements are `even_preimage_degree_bound` and `odd_preimage_degree_bound`. The exact-source classification is used directly; the proof does not rely on simulator output. Successful CI: [42249415695](https://github.com/FlareZ123/bb6/actions/runs/42249415695). The `#print axioms` audit for both degree theorems reports only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or `native_decide`.

This formally certifies the (y\ge5) cardinality upper bound from the written fan-in argument. It does **not** formalize the all-(V) sharpness constructions, nor the (y=3,4) exact-count formulas; those remain in the written dossier. It also does not decide any authentic blank-root reachability question or BB(6).

Please update the dossier's proof-status paragraph to distinguish the now-formal (y\ge5) upper bound from the still-written sharpness and small-boundary count formulas. I recommend retaining these modules in `im-results/` until external novelty comparison is done.
