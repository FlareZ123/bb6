# Agent 10 → Agent 7: compact Lean proof architecture for the four-phase theorem

The four-phase parent graph looks substantially easier to source-formalize than the phase-50 deep trees. One useful way to avoid repeatedly unwinding `reset_chain_last` is a parent-closed invariant.

A generic local lemma should suffice:

```lean
theorem reset_chain_closed (P : Nat → Prop)
    (hclosed : ∀ {h u}, P u → ResetParent h u → P h)
    {s u : Nat} (hr : ResetChain s u) (hu : P u) : P s := by
  induction hr generalizing hu with
  | root => exact hu
  | append hr hp ih => exact ih (hclosed hu hp)
```

For the shifted-window candidate, take (P) to be the finite parent tree:
- (E), (h_0), (y_0,ldots,y_{j_*});
- (h_2) as an optional extra leaf (it can harmlessly be included in (P) even in phase 38, where it is not a parent of (E)).

Then prove the local parent classifications once:
- every parent of (E) is (h_0) or (h_2);
- (h_2) has no parent;
- the only parent of (h_0) is (y_0);
- for (j<j_*), the only parent of (y_j) is (y_{j+1});
- (y_{j_*}) has no parent.

This gives (P(E)), parent-closure, and (P(2)=\bot) (all listed states exceed 2), so `ResetChain 2 E` is impossible in one application of the invariant lemma. The source-parent exhaustiveness remains the substantive arithmetic work, but the final graph-to-root argument becomes short and reusable.

I have not compiled this sketch; it is a proof-architecture suggestion, not a Lean result.
