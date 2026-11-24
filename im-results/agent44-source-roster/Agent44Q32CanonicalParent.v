From BusyCoq Require Import Enumerate62 Eqb Individual62
  Agent8QueueCheckpoint Agent8PackedChunk2_32_32 Agent32SourceEncoding.
From Coq Require Import List Bool Strings.String NArith.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.

(* This is canonicalResidualRoster[7] in the Agent 13 JSON export:
   raw residual 11, address B0=1RC then C0=0LA, depth 2, nine holes.
   Keep the literal source table here so the original Coq parser, rather
   than a Lean-side approximation, determines its semantics. *)
Definition q32_canonical_residual_7 : TM :=
  TM_from_str "1RB---_1RC---_0LA---_------_------_------".

(* Finite executable form of the original source is_child_of relation. *)
Definition q32_source_refinesb (child parent : TM) : bool :=
  forallb (fun q => forallb (fun s =>
    match parent (q,s) with
    | None => true
    | Some v => BusyCoq.Eqb.eqb (child (q,s)) (Some v)
    end) all_syms) all_qs.

Theorem q32_source_refinesb_spec child parent :
  q32_source_refinesb child parent = true <-> is_child_of child parent.
Proof.
  unfold q32_source_refinesb.
  split.
  - intros H [q s].
    apply forallb_forall with (x:=q) in H; [|apply all_qs_spec].
    apply forallb_forall with (x:=s) in H; [|apply all_syms_spec].
    destruct (parent (q,s)) as [v|] eqn:E.
    + right. destruct (BusyCoq.Eqb.eqb_spec (child (q,s)) (Some v)); congruence.
    + left. reflexivity.
  - intros H.
    apply forallb_forall. intros q _.
    apply forallb_forall. intros s _.
    destruct (parent (q,s)) as [v|] eqn:E; [|reflexivity].
    destruct (H (q,s)) as [Hnone|Heq]; [congruence|].
    destruct (BusyCoq.Eqb.eqb_spec (child (q,s)) (Some v)); congruence.
Qed.

Definition q32_active_refines_residual_7b : bool :=
  forallb (fun x => q32_source_refinesb (tm x) q32_canonical_residual_7)
    (fst (decode_queue packed_chunk_2_32_32)).

Theorem q32_active_refines_residual_7b_true :
  q32_active_refines_residual_7b = true.
Proof. vm_compute. reflexivity. Qed.

Theorem q32_active_count :
  length (fst (decode_queue packed_chunk_2_32_32)) = 84%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem q32_active_refines_canonical_residual_7 :
  Forall (fun x => is_child_of (tm x) q32_canonical_residual_7)
    (fst (decode_queue packed_chunk_2_32_32)).
Proof.
  apply Forall_forall. intros x Hx.
  apply q32_source_refinesb_spec.
  unfold q32_active_refines_residual_7b in q32_active_refines_residual_7b_true.
  apply forallb_forall with (x:=x) in q32_active_refines_residual_7b_true;
    [exact q32_active_refines_residual_7b_true|exact Hx].
Qed.

Theorem q32_checkpoint_refines_canonical_residual_7 :
  Forall (fun x => is_child_of (tm x) q32_canonical_residual_7)
    (fst (SearchQueue_upds decider (q_i 2 32) 32%N)).
Proof.
  rewrite packed_chunk_2_32_32_exact.
  exact q32_active_refines_canonical_residual_7.
Qed.

Theorem q32_canonical_residual_7_extends_root :
  is_child_of q32_canonical_residual_7 (tm node0).
Proof.
  apply q32_source_refinesb_spec.
  vm_compute. reflexivity.
Qed.

Theorem q32_checkpoint_refines_root :
  Forall (fun x => is_child_of (tm x) (tm node0))
    (fst (SearchQueue_upds decider (q_i 2 32) 32%N)).
Proof.
  apply Forall_forall. intros x Hx.
  eapply child_trans.
  - apply Forall_forall with (x:=x) in q32_checkpoint_refines_canonical_residual_7;
      [exact q32_checkpoint_refines_canonical_residual_7|exact Hx].
  - exact q32_canonical_residual_7_extends_root.
Qed.

Theorem q32_canonical_residual_7_source_roundtrip :
  forall s, TM_from_str (TM_to_str q32_canonical_residual_7) s =
    q32_canonical_residual_7 s.
Proof. apply agent32_table_roundtrip. Qed.

Print Assumptions q32_active_refines_canonical_residual_7.
Print Assumptions q32_checkpoint_refines_canonical_residual_7.
Print Assumptions q32_checkpoint_refines_root.
Print Assumptions q32_canonical_residual_7_source_roundtrip.
