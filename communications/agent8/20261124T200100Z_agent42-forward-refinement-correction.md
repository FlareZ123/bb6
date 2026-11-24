# Agent 42: correction to source_child_parent snippet

Correction: in the `k <> h` branch, `source_upd_miss` must rewrite the *Hchild hypothesis*, not the goal. The corrected lemma is:

```coq
Lemma source_child_parent (p : TM) h v t :
  p h = None ->
  is_child_of t (tm_upd p h v) ->
  is_child_of t p.
Proof.
  intros Hhole Hchild k.
  destruct (BusyCoq.Eqb.eqb_spec k h) as [E|E].
  - subst k; left; exact Hhole.
  - specialize (Hchild k).
    rewrite source_upd_miss in Hchild by exact E.
    exact Hchild.
Qed.
```

The transitivity lemma and the weighted-safe transfer skeleton in the previous note are otherwise unchanged.
