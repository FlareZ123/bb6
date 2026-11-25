From BusyCoq Require Import Enumerate62 TC62 Agent32Q0Partition
  Agent32SourceBackwards Agent8AdaptiveSource Agent8QueueCheckpoint
  Agent8WeightedSource Agent8GlobalSource Agent8SourceWF Individual62.
From Coq Require Import List NArith Lia.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* Each of the exact source slices may choose its own finite adaptive plan.
   Neither the fuel nor the number of remaining nodes needs to agree.
   The only global partition premise is the proved coverage of actual q_0. *)
Theorem actual_source_chunks_adaptive_coverage (Safe : T -> Prop)
    (plans : nat -> AdaptivePlan) :
  (forall x, match decider (tm x) with
    | TC62.TM.Halt h => Forall Safe (expand' x h) -> Safe x
    | TC62.TM.NonHalt => Safe x
    | TC62.TM.Unknown => True
    end) ->
  (forall i, i < 129 ->
    Forall Safe (adaptive_obligations decider (plans i) (q_i (100*i) 100))) ->
  Safe node0.
Proof.
  intros Hlocal Hchunks.
  apply (actual_source_adaptive_coverage Safe AP_stop Hlocal).
  cbn [adaptive_obligations].
  apply Forall_app. split.
  - apply Forall_forall. intros x Hx.
    destruct (agent32_q0_chunk_cover x Hx) as [i [Hi Hxi]].
    pose proof (adaptive_plan_sound Safe decider Hlocal (plans i)
      (q_i (100*i) 100) (Hchunks i Hi)) as Hq.
    exact (proj1 (Forall_forall Safe _) (proj1 Hq) x Hxi).
  - rewrite agent32_q0_holdout_empty. constructor.
Qed.

(* The packed lists must match actual source updates by equality, not
   by hash, count, membership alone, or external simulation. *)
Theorem actual_source_chunks_packed_coverage (Safe : T -> Prop)
    (fuel : nat -> N) (packed : nat -> packed_queue)
    (plans : nat -> AdaptivePlan) :
  (forall x, match decider (tm x) with
    | TC62.TM.Halt h => Forall Safe (expand' x h) -> Safe x
    | TC62.TM.NonHalt => Safe x
    | TC62.TM.Unknown => True
    end) ->
  (forall i, i < 129 ->
    encode_queue (SearchQueue_upds decider (q_i (100*i) 100) (fuel i)) = packed i) ->
  (forall i, i < 129 ->
    Forall Safe (adaptive_obligations decider (plans i) (decode_queue (packed i)))) ->
  Safe node0.
Proof.
  intros Hlocal Hpacked Hres.
  apply (actual_source_chunks_adaptive_coverage Safe
    (fun i => AP_advance (fuel i) (plans i)) Hlocal).
  intros i Hi. cbn [adaptive_obligations].
  rewrite (source_checkpoint_decode decider (q_i (100*i) 100)
    (fuel i) (packed i) (checkpoint_chunk_canonical (100*i) 100)
    (Hpacked i Hi)).
  exact (Hres i Hi).
Qed.

(* An actual complete upper bound follows if every independently
   scheduled residual is safe at the proposed bound, including the
   original active and held nodes whenever a plan stops. *)
Theorem actual_source_chunks_packed_global_upper (bound : nat)
    (fuel : nat -> N) (packed : nat -> packed_queue)
    (plans : nat -> AdaptivePlan) :
  N.to_nat 1000000 + 6 <= bound ->
  (forall i, i < 129 ->
    encode_queue (SearchQueue_upds decider (q_i (100*i) 100) (fuel i)) = packed i) ->
  (forall i, i < 129 ->
    Forall (source_weighted_safe bound)
      (adaptive_obligations decider (plans i) (decode_queue (packed i)))) ->
  forall t : TM, forall n, halts_in t c0 n -> S n <= bound.
Proof.
  intros Hmargin Hpacked Hres.
  apply weighted_normalization_global; [lia|].
  intros t Hroot.
  pose proof (actual_source_chunks_packed_coverage
    (source_weighted_safe bound) fuel packed plans
    (source_weighted_local bound Hmargin) Hpacked Hres) as Hsafe.
  exact (Hsafe source_root_good t (source_root_child t Hroot)).
Qed.

Print Assumptions actual_source_chunks_adaptive_coverage.
Print Assumptions actual_source_chunks_packed_coverage.
Print Assumptions actual_source_chunks_packed_global_upper.
