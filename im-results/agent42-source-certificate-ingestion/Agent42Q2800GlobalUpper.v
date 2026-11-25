From BusyCoq Require Import Enumerate62 Individual62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RecoveredHeld Agent42HeldCheckpointMembership Agent5HeldFARBatch Agent5RosterComplement Agent42Q2800BatchWitnesses Agent5ChunkCoverage.
From Coq Require Import List NArith Lia.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* Consume the exact q_i(2800,100) source checkpoint reduction inside the
   actual 129-chunk upper-bound theorem. The q2800 roster consists of 95
   source-tree certificates and the recovered FARv3 held leaf; its exact
   residual list has 89 obligations. No other source chunk is shortened. *)
Theorem actual_source_chunks_packed_global_upper_after_q2800_roster
    (bound : nat) (fuel : nat -> N) (packed : nat -> packed_queue)
    (plans : nat -> AdaptivePlan) :
    1000006 <= bound ->
    (forall i, i < 129 ->
      encode_queue (SearchQueue_upds decider (q_i (100*i) 100) (fuel i)) =
        packed i) ->
    fuel 28 = 1000000%N ->
    plans 28 = AP_stop ->
    Forall (source_weighted_safe bound) q2800_residual_obligations ->
    (forall i, i < 129 -> i <> 28 ->
      Forall (source_weighted_safe bound)
        (adaptive_obligations decider (plans i) (decode_queue (packed i)))) ->
    forall t : TM, forall n, halts_in t c0 n -> S n <= bound.
Proof.
  intros Hbound Hpacked Hfuel28 Hplan28 Hres28 HresOther.
  apply actual_source_chunks_packed_global_upper
    with (fuel := fuel) (packed := packed) (plans := plans).
  - change (N.to_nat 1000000 + 6 <= bound).
    lia.
  - exact Hpacked.
  - intros i Hi.
    destruct (Nat.eq_dec i 28) as [Heq|Hne].
    + subst i.
      rewrite Hplan28.
      rewrite (source_checkpoint_decode decider (q_i (100*28) 100)
        (fuel 28) (packed 28) (checkpoint_chunk_canonical (100*28) 100)
        (Hpacked 28 ltac:(lia))).
      rewrite Hfuel28.
      exact
        ((proj2 (q2800_adaptive_obligations_safe_iff_residual bound Hbound))
          Hres28).
    + exact (HresOther i Hi Hne).
Qed.

Print Assumptions actual_source_chunks_packed_global_upper_after_q2800_roster.


(* Exact table-level bridge: the same recovered held machine is a node of
   the original q_i(2800,100) checkpoint and a member of Agent 5's independently
   checked source-safe held roster. *)
Definition q2800_held_attempt : held_attempt :=
  Build_held_attempt "2800" recovered_held_2800 true
    (RWL_mod_FAR 20000 10000 3 3200 2 4 2 0).

Lemma q2800_held_attempt_in :
  In q2800_held_attempt held_attempts.
Proof.
  unfold q2800_held_attempt, held_attempts.
  simpl.
  right; right; right; right; right; right; right; left.
  reflexivity.
Qed.

Lemma q2800_held_attempt_passes :
  held_check q2800_held_attempt = true.
Proof.
  unfold q2800_held_attempt, held_check.
  vm_compute.
  reflexivity.
Qed.

Theorem recovered_held_2800_in_held_certified_roster :
  In recovered_held_2800 held_certified_roster.
Proof.
  unfold held_certified_roster.
  apply in_map_iff.
  exists q2800_held_attempt.
  split.
  - reflexivity.
  - apply filter_In.
    split.
    + exact q2800_held_attempt_in.
    + exact q2800_held_attempt_passes.
Qed.

Theorem q2800_held_leaf_checkpoint_and_agent5_roster :
  exists x,
    In x (snd recovered_held_2800_checkpoint) /\
    is_child_of (tm x) recovered_held_2800 /\
    is_child_of recovered_held_2800 (tm x) /\
    In recovered_held_2800 held_certified_roster.
Proof.
  destruct recovered_held_2800_checkpoint_leaf as [x [Hx [Hf Hb]]].
  exists x.
  repeat split; try assumption.
  exact recovered_held_2800_in_held_certified_roster.
Qed.

(* Compose Agent 5's accepted held-table roster with the 95 q2800 source-tree
   certificates. Coverage is proved by the exact source_roster_covers
   refinement predicate, not inferred from list counts. *)
Definition q2800_augmented_roster : list TM :=
  held_certified_roster ++ q2800_tree_roster.

Theorem q2800_augmented_roster_safe (bound : nat) :
  (1000006 <= bound)%nat ->
  Forall (source_table_safe bound) q2800_augmented_roster.
Proof.
  intros Hbound.
  unfold q2800_augmented_roster.
  rewrite Forall_app.
  split.
  - exact (held_certified_roster_safe bound).
  - apply q2800_tree_roster_safe.
    exact Hbound.
Qed.

Theorem actual_source_chunks_packed_global_upper_after_q2800_augmented_roster
    bound (fuel : nat -> N) (packed : nat -> packed_queue)
    (plans : nat -> AdaptivePlan) :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  (forall i, (i < 129)%nat ->
     encode_queue (SearchQueue_upds decider (q_i (100*i) 100) (fuel i)) = packed i) ->
  (forall i, (i < 129)%nat ->
     Forall (source_weighted_safe bound)
       (roster_remaining q2800_augmented_roster
         (adaptive_obligations decider (plans i) (decode_queue (packed i))))) ->
  forall t : TM, forall n, halts_in t c0 n -> (S n <= bound)%nat.
Proof.
  intros Hmargin Hpacked Hrest.
  eapply (roster_filtered_global_upper bound q2800_augmented_roster fuel packed plans).
  - exact Hmargin.
  - apply q2800_augmented_roster_safe.
    lia.
  - exact Hpacked.
  - exact Hrest.
Qed.

Print Assumptions q2800_held_attempt_passes.
Print Assumptions recovered_held_2800_in_held_certified_roster.
Print Assumptions q2800_held_leaf_checkpoint_and_agent5_roster.
Print Assumptions q2800_augmented_roster_safe.
Print Assumptions actual_source_chunks_packed_global_upper_after_q2800_augmented_roster.
