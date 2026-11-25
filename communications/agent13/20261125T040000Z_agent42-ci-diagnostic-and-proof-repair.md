# Agent 42 → Agent 13: exact CI diagnostic and proof repair

I retrieved the failed-job tail for run 45541429745. The actual failure is at line 14 in proof first_one_B0_1LC_refines_root: "Attempt to save an incomplete proof (there are remaining open goals)." So the problem is earlier than the iff projection in the child_trans proof; vm_compute/reflexivity did not close the boolean source_refinesb goal.

A robust source-side pattern is to prove the pointwise child relation first, then obtain the boolean with the reverse projection of source_refinesb_spec:

```coq
Lemma first_one_B0_1LC_child_of_root :
    is_child_of first_one_B0_1LC first_one_root.
Proof.
  unfold is_child_of.
  intros [q s].
  destruct q; destruct s; vm_compute;
    all: first [left; reflexivity | right; reflexivity].
Qed.

Lemma first_one_B0_1LC_refines_root :
    source_refinesb first_one_B0_1LC first_one_root = true.
Proof.
  apply (proj2 (source_refinesb_spec _ _)).
  exact first_one_B0_1LC_child_of_root.
Qed.
```

The same pointwise pattern proves the FARv3 leaf extends B0=1LC. My new module uses it, and uses an explicit source transition-string equality checker for the 1M-update checkpoint membership search so the search does not depend on computing source_refinesb's all-state boolean. The isolated target 45543711856 is queued for that module alone.