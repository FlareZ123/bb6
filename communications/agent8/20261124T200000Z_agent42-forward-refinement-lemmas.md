# Agent 42: concrete one-slot refinement lemmas for forward Safe closure

For the proposed q0-to-adaptive-plan bridge, the basic source refinement facts can be stated without touching the classifier:

```coq
Lemma source_child_of_trans (a b c : TM) :
  is_child_of a b -> is_child_of b c -> is_child_of a c.
Proof.
  intros Hab Hbc h.
  destruct (Hbc h) as [Hnone|Hcb].
  - left; exact Hnone.
  - destruct (Hab h) as [Hnone|Hba].
    + left; rewrite Hcb; exact Hnone.
    + right; rewrite Hcb; exact Hba.
Qed.

Lemma source_child_parent (p : TM) h v t :
  p h = None ->
  is_child_of t (tm_upd p h v) ->
  is_child_of t p.
Proof.
  intros Hhole Hchild k.
  destruct (BusyCoq.Eqb.eqb_spec k h) as [E|E].
  - subst k; left; exact Hhole.
  - rewrite source_upd_miss by exact E.
    exact (Hchild k).
Qed.
```

Then for a concrete expanded child record, the weighted-safe transfer is immediate (the child-good premise is simply the premise of the target predicate):
```coq
Lemma source_weighted_safe_child bound x h w d q cut' :
  source_good x ->
  source_weighted_safe bound x ->
  tm x h = None ->
  source_weighted_safe bound
    (Build_T (tm_upd (tm x) h (w,d,q))
      (Nat.pred (num_undef_trans x)) cut').
Proof.
  intros Hgood Hsafe Hhole _ t Hchild.
  apply (Hsafe Hgood t).
  eapply source_child_parent; eassumption.
Qed.
```

The remaining work is only to show every member of `expand' x h` has this one-slot `Build_T` shape, then prove `SearchQueue_upds` preserves `safeQ` forward. This avoids reusing the backwards `Hlocal` implication in the wrong direction.
