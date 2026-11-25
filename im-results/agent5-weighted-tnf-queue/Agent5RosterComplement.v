From BusyCoq Require Import Enumerate62 Individual62 SourceResidualRoster
  Agent8WeightedSource Agent8AdaptiveSource Agent8QueueCheckpoint Agent5ChunkCoverage.
From Coq Require Import List Bool NArith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

Definition roster_remaining (roster : list TM) (xs : list T) : list T :=
  filter (fun x => negb (source_roster_covers roster x)) xs.

Theorem roster_remaining_safe_iff bound roster xs :
  Forall (source_table_safe bound) roster ->
  (Forall (source_weighted_safe bound) xs <->
   Forall (source_weighted_safe bound) (roster_remaining roster xs)).
Proof.
  intros Hroster.
  rewrite !Forall_forall.
  split.
  - intros H x Hx. unfold roster_remaining in Hx.
    apply filter_In in Hx as [Hin _]. exact (H x Hin).
  - intros H x Hx.
    destruct (source_roster_covers roster x) eqn:Hcov.
    + eapply source_roster_safe; eassumption.
    + apply H. unfold roster_remaining. apply filter_In.
      split; [exact Hx|rewrite Hcov; reflexivity].
Qed.

Theorem roster_removed_exact roster xs x :
  In x (roster_remaining roster xs) <->
  In x xs /\ source_roster_covers roster x = false.
Proof.
  unfold roster_remaining. rewrite filter_In, negb_true_iff. reflexivity.
Qed.

(* The generic consumer acts on an exact decoded checkpoint. It includes
   both active and held nodes, including unprocessed descendants. *)
Theorem roster_checkpoint_consumption
    (bound : nat) (roster : list TM) (offset size : nat)
    (fuel : N) (packed : packed_queue) :
  Forall (source_table_safe bound) roster ->
  SearchQueue_upds decider (q_i offset size) fuel = decode_queue packed ->
  (Forall (source_weighted_safe bound)
      (adaptive_obligations decider (AP_advance fuel AP_stop) (q_i offset size))
   <->
   Forall (source_weighted_safe bound)
      (roster_remaining roster (fst (decode_queue packed) ++ snd (decode_queue packed)))).
Proof.
  intros Hroster Hpacked.
  change (Forall (source_weighted_safe bound)
      (fst (SearchQueue_upds decider (q_i offset size) fuel) ++
       snd (SearchQueue_upds decider (q_i offset size) fuel)) <-> _).
  rewrite Hpacked. apply roster_remaining_safe_iff. exact Hroster.
Qed.

Theorem roster_filtered_global_upper bound roster
    (fuel : nat -> N) (packed : nat -> packed_queue)
    (plans : nat -> AdaptivePlan) :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) roster ->
  (forall i, i < 129 ->
     encode_queue (SearchQueue_upds decider (q_i (100*i) 100) (fuel i)) = packed i) ->
  (forall i, i < 129 ->
     Forall (source_weighted_safe bound)
       (roster_remaining roster (adaptive_obligations decider (plans i) (decode_queue (packed i))))) ->
  forall t : TM, forall n, halts_in t c0 n -> S n <= bound.
Proof.
  intros Hmargin Hroster Hpacked Hrest.
  apply (actual_source_chunks_packed_global_upper bound fuel packed plans Hmargin Hpacked).
  intros i Hi.
  apply (proj2 (roster_remaining_safe_iff bound roster _ Hroster)).
  exact (Hrest i Hi).
Qed.

Print Assumptions roster_remaining_safe_iff.
Print Assumptions roster_checkpoint_consumption.
Print Assumptions roster_filtered_global_upper.
