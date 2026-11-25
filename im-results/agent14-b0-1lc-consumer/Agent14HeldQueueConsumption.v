From BusyCoq Require Import Agent42HeldCheckpointMembership Agent5ChunkCoverage.
From Coq Require Import List Bool Arith NArith Lia.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* The held FARv3 table is an exact source transition table. Any source
   obligation with this exact table is already safe for every bound. *)

Definition without_recovered_held_2800 (xs : list T) : list T :=
  filter
    (fun x => negb (source_table_eqb (tm x) recovered_held_2800))
    xs.

Definition with_recovered_held_2800 (xs : list T) : list T :=
  filter
    (fun x => source_table_eqb (tm x) recovered_held_2800)
    xs.

Lemma Forall_filter_partition {A : Type} (f : A -> bool) (P : A -> Prop)
    (xs : list A) :
    Forall P xs <->
      Forall P (filter f xs) /\
      Forall P (filter (fun x => negb (f x)) xs).
Proof.
  split.
  - intro Hall.
    apply Forall_forall in Hall.
    split; apply Forall_forall; intros x Hx;
      apply filter_In in Hx as [Hin _];
      exact (Hall x Hin).
  - intros [Hyes Hno].
    apply Forall_forall in Hyes.
    apply Forall_forall in Hno.
    apply Forall_forall.
    intros x Hx.
    destruct (f x) eqn:Hfx.
    + apply Hyes.
      apply filter_In.
      split; [exact Hx|exact Hfx].
    + apply Hno.
      apply filter_In.
      split; [exact Hx|].
      simpl.
      rewrite Hfx.
      reflexivity.
Qed.

(* The exact-table filter is sound for every list, not only for the
   q_i(2800,100) checkpoint. The proof uses the source-table equality
   specification and the original FARv3 source-roster safety theorem. *)
Theorem recovered_held_2800_filter_safe (bound : nat) (xs : list T) :
    Forall (source_weighted_safe bound)
      (with_recovered_held_2800 xs).
Proof.
  apply Forall_forall.
  intros x Hx.
  unfold with_recovered_held_2800 in Hx.
  apply filter_In in Hx as [_ Hmatch].
  apply recovered_held_2800_checkpoint_leaf_safe with (x := x).
  exact (proj1 (source_table_eqb_spec (tm x) recovered_held_2800) Hmatch).
Qed.

(* Consuming every exact copy of the held table is logically equivalent to
   proving the remaining list safe: no other active or held node is removed. *)
Theorem source_weighted_safe_iff_without_recovered_held_2800
    (bound : nat) (xs : list T) :
    Forall (source_weighted_safe bound) xs <->
    Forall (source_weighted_safe bound)
      (without_recovered_held_2800 xs).
Proof.
  pose proof
    (Forall_filter_partition
      (fun x => source_table_eqb (tm x) recovered_held_2800)
      (source_weighted_safe bound) xs) as Hpartition.
  unfold without_recovered_held_2800.
  split.
  - intro H.
    apply (proj2 Hpartition) in H as [_ Hrest].
    exact Hrest.
  - intro Hrest.
    apply (proj1 Hpartition).
    split.
    + exact (recovered_held_2800_filter_safe bound xs).
    + exact Hrest.
Qed.

Definition q0_2800_adaptive_obligations : list T :=
  adaptive_obligations decider
    (AP_advance 1000000%N AP_stop) (q_i 2800 100).

Definition q0_2800_consumed_obligations : list T :=
  with_recovered_held_2800 q0_2800_adaptive_obligations.

Definition q0_2800_residual_obligations : list T :=
  without_recovered_held_2800 q0_2800_adaptive_obligations.

Theorem q0_2800_consumed_obligations_safe (bound : nat) :
    Forall (source_weighted_safe bound) q0_2800_consumed_obligations.
Proof.
  exact (recovered_held_2800_filter_safe bound q0_2800_adaptive_obligations).
Qed.

Theorem q0_2800_queue_safe_iff (bound : nat) :
    Forall (source_weighted_safe bound) q0_2800_adaptive_obligations <->
    Forall (source_weighted_safe bound) q0_2800_residual_obligations.
Proof.
  unfold q0_2800_adaptive_obligations, q0_2800_residual_obligations,
    without_recovered_held_2800.
  apply source_weighted_safe_iff_without_recovered_held_2800.
Qed.

Theorem q0_2800_consumed_exact (x : T) :
    In x q0_2800_consumed_obligations <->
    In x q0_2800_adaptive_obligations /\
      source_table_eqb (tm x) recovered_held_2800 = true.
Proof.
  unfold q0_2800_consumed_obligations, with_recovered_held_2800.
  apply filter_In.
Qed.

Theorem q0_2800_residual_exact (x : T) :
    In x q0_2800_residual_obligations <->
    In x q0_2800_adaptive_obligations /\
      source_table_eqb (tm x) recovered_held_2800 = false.
Proof.
  unfold q0_2800_residual_obligations, without_recovered_held_2800.
  rewrite filter_In.
  simpl.
  rewrite negb_true_iff.
  tauto.
Qed.

(* The actual source checkpoint contains the held table, and therefore the
   consumed part is nonempty. This uses the original source queue computation,
   not a copied table count. *)
Theorem q0_2800_consumed_nonempty :
    exists x, In x q0_2800_consumed_obligations.
Proof.
  pose proof recovered_held_2800_checkpoint_member as H.
  unfold recovered_held_2800_checkpoint_memberb,
    recovered_held_2800_checkpoint in H.
  apply existsb_exists in H.
  destruct H as [x [Hx Hmatch]].
  exists x.
  unfold q0_2800_consumed_obligations, with_recovered_held_2800,
    q0_2800_adaptive_obligations.
  apply filter_In.
  split.
  - unfold adaptive_obligations.
    change In x
      (fst recovered_held_2800_checkpoint ++
       snd recovered_held_2800_checkpoint).
    apply in_or_app.
    right.
    exact Hx.
  - exact Hmatch.
Qed.

(* The checkpoint's exact table occurs once. All other active/held entries
   remain in q0_2800_residual_obligations. *)
Theorem q0_2800_consumed_count :
    length q0_2800_consumed_obligations = 1.
Proof.
  unfold q0_2800_consumed_obligations, with_recovered_held_2800,
    q0_2800_adaptive_obligations.
  vm_compute.
Qed.

Theorem q0_2800_residual_count :
    length q0_2800_residual_obligations =
      length q0_2800_adaptive_obligations - 1.
Proof.
  unfold q0_2800_residual_obligations, without_recovered_held_2800,
    q0_2800_adaptive_obligations.
  vm_compute.
Qed.

(* Drop only the exact q_i(2800,100) held table from chunk 28's adaptive
   obligations. All other 128 chunks retain their original full lists.
   The existing packed global-upper consumer then applies unchanged. *)
Theorem actual_source_chunks_packed_global_upper_after_held_consumption
    (bound : nat) (fuel : nat -> N) (packed : nat -> packed_queue)
    (plans : nat -> AdaptivePlan) :
    N.to_nat 1000000 + 6 <= bound ->
    (forall i, i < 129 ->
      encode_queue (SearchQueue_upds decider (q_i (100*i) 100) (fuel i)) =
        packed i) ->
    (forall i, i < 129 ->
      Forall (source_weighted_safe bound)
        (if Nat.eq_dec i 28 then
          without_recovered_held_2800
            (adaptive_obligations decider (plans i) (decode_queue (packed i)))
         else
          adaptive_obligations decider (plans i) (decode_queue (packed i)))) ->
    forall t : TM, forall n, halts_in t c0 n -> S n <= bound.
Proof.
  intros Hmargin Hpacked Hres.
  apply actual_source_chunks_packed_global_upper with
    (fuel := fuel) (packed := packed) (plans := plans).
  - exact Hmargin.
  - exact Hpacked.
  - intros i Hi.
    destruct (Nat.eq_dec i 28) as [Heq|Hne].
    + subst i.
      apply
        (proj2
          (source_weighted_safe_iff_without_recovered_held_2800 bound
            (adaptive_obligations decider (plans 28) (decode_queue (packed 28))))).
      exact (Hres 28 Hi).
    + exact (Hres i Hi).
Qed.

Print Assumptions recovered_held_2800_filter_safe.
Print Assumptions source_weighted_safe_iff_without_recovered_held_2800.
Print Assumptions q0_2800_queue_safe_iff.
Print Assumptions q0_2800_consumed_nonempty.
Print Assumptions q0_2800_consumed_count.
Print Assumptions q0_2800_residual_count.
Print Assumptions actual_source_chunks_packed_global_upper_after_held_consumption.
