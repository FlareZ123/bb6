(* Exact q_i(2800,100) active-node source-tree cover.
   Generated from the packed original-source checkpoint at fuel 1,000,000.
   Search horizon: 80 macro steps; all certificates are checked by source_tree_check. *)

From BusyCoq Require Import Enumerate62 Individual62 Agent8AdaptiveSource
  Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster
  Agent47SourceTree Agent47SourceWitness Agent42HeldCheckpointMembership.
From Coq Require Import List Bool Strings.String Lia NArith.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Theorem q2800_trees_checked :
  forallb (q2800_tree_check 1000006) q2800_trees = true.
Proof.
  unfold q2800_trees.
  repeat rewrite forallb_app.
  rewrite q2800_trees_shard01_checked,
    q2800_trees_shard02_checked,
    q2800_trees_shard03_checked,
    q2800_trees_shard04_checked,
    q2800_trees_shard05_checked.
  reflexivity.
Qed.

Theorem q2800_tree_roster_safe_1000006 :
  Forall (source_table_safe 1000006) q2800_tree_roster.
Proof.
  apply Forall_forall.
  intros p Hp.
  unfold q2800_tree_roster in Hp.
  apply in_map_iff in Hp.
  destruct Hp as [[s t] [Hp HIn]].
  simpl in Hp.
  subst p.
  apply q2800_tree_check_sound.
  eapply forallb_forall.
  - exact q2800_trees_checked.
  - exact HIn.
Qed.

Lemma q2800_source_table_safe_mono (b b' : nat) (p : TM) :
  b <= b' ->
  source_table_safe b p ->
  source_table_safe b' p.
Proof.
  unfold source_table_safe, weighted_bound.
  intros Hle Hsafe m Hchild n k s Hhalts Hzero Hk.
  specialize (Hsafe m Hchild n k s Hhalts Hzero Hk).
  lia.
Qed.

Theorem q2800_tree_roster_safe (bound : nat) :
  1000006 <= bound ->
  Forall (source_table_safe bound) q2800_tree_roster.
Proof.
  intros Hbound.
  apply Forall_forall.
  intros p Hp.
  apply Forall_forall with (x := p) in q2800_tree_roster_safe_1000006.
  - eapply q2800_source_table_safe_mono; eauto.
  - exact Hp.
Qed.

Definition q2800_safe_roster : list TM :=
  q2800_tree_roster ++ [recovered_held_2800].

Theorem q2800_safe_roster_safe (bound : nat) :
  1000006 <= bound ->
  Forall (source_table_safe bound) q2800_safe_roster.
Proof.
  intros Hbound.
  unfold q2800_safe_roster.
  apply Forall_app.
  split.
  - apply q2800_tree_roster_safe.
    exact Hbound.
  - constructor.
    + apply recovered_held_2800_safe.
    + constructor.
Qed.

Definition q2800_checkpoint_obligations : list T :=
  fst recovered_held_2800_checkpoint ++ snd recovered_held_2800_checkpoint.

Theorem q2800_checkpoint_obligations_exact :
  adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 2800 100) =
    q2800_checkpoint_obligations.
Proof.
  unfold adaptive_obligations, q2800_checkpoint_obligations.
  rewrite recovered_held_2800_checkpoint_exact.
  reflexivity.
Qed.

Definition q2800_residual_obligations : list T :=
  source_uncovered q2800_safe_roster q2800_checkpoint_obligations.

Theorem q2800_residual_count :
  length q2800_residual_obligations = 89.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem q2800_adaptive_obligations_safe_iff_residual (bound : nat) :
  1000006 <= bound ->
  (Forall (source_weighted_safe bound)
      (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 2800 100)) <->
   Forall (source_weighted_safe bound) q2800_residual_obligations).
Proof.
  intros Hbound.
  rewrite q2800_checkpoint_obligations_exact.
  split.
  - intros Hfull.
    apply Forall_forall.
    intros x Hx.
    apply Forall_forall with (x := x) in Hfull.
    + exact Hfull.
    + unfold q2800_residual_obligations in Hx.
      apply filter_In in Hx as [Hin _].
      exact Hin.
  - intros Hres.
    eapply source_uncovered_sound.
    + apply q2800_safe_roster_safe.
      exact Hbound.
    + exact Hres.
Qed.

Print Assumptions q2800_trees_checked.
Print Assumptions q2800_tree_roster_safe.
Print Assumptions q2800_residual_count.
Print Assumptions q2800_adaptive_obligations_safe_iff_residual.
