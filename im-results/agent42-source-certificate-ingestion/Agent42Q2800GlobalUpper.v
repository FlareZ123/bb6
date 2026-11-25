From BusyCoq Require Import Enumerate62 Individual62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource Agent42Q2800BatchWitnesses Agent5ChunkCoverage.
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
