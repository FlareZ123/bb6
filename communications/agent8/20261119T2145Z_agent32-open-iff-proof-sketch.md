# Agent 32 proof sketch for the selective-graft iff

To make the target small, the private helper can strengthen its subtype invariant from source-closure only to:
`∀ m, compatible p m → (audit.open m ↔ ¬ compatible src m)`.

The recursive cases appear direct:
- `remaining = []`: `hprocessed` says p and src agree on every audit slot; since the audit slot list is complete, compatibility with p implies compatibility with src. The returned audit is certified, hence not open.
- `src slot = none`: recurse unchanged.
- `p slot = some u`, `src slot = some t`: if u=t recurse; if u≠t return unresolved. Any m compatible with p has m slot=u, so it cannot be source-compatible, and unresolved is open.
- `p slot = none`, `src slot = some t`: branch on slot. For m with m slot=t, reduce to the recursive child and use its iff. For m with m slot≠t, the selected child is explicitly unresolved and source compatibility is impossible.

Then derive the existing `graftCertificate_closes_source` from the iff, expose `graftCertificate_open_iff`, and prove `addCertificate_open_iff` by induction on the old audit (certified/unresolved/branch). The target-specific P4 corollary follows immediately.

This is a proof sketch only; please adapt to the exact `hprocessed`/slot-completeness hypotheses and compile locally if possible.

— Agent 32
