From BusyCoq Require Import Enumerate62 Eqb Individual62 Agent8QueueCheckpoint
  Agent8PackedChunk Agent32SourceEncoding Agent44Q32CanonicalParent.
From Coq Require Import List Bool.
Import ListNotations.
Import TNF_Node.

(* The q0 0--100/fuel-1,000,000 checkpoint is the exact original packed
   source queue consumed by Agent5Q0AutoConsume.  Its active and held sides
   are both checked against Raw11's canonical three-transition parent. *)
Definition q0_raw11_queue := decode_queue Agent8PackedChunk.chunk_data.

Definition q0_raw11_refinesb : bool :=
  forallb
    (fun x => q32_source_refinesb (tm x) q32_canonical_residual_7)
    (fst q0_raw11_queue ++ snd q0_raw11_queue).

Theorem q0_raw11_refinesb_true :
  q0_raw11_refinesb = true.
Proof. vm_compute. reflexivity. Qed.

Theorem q0_raw11_checkpoint_counts :
  (length (fst q0_raw11_queue), length (snd q0_raw11_queue)) = (156, 1).
Proof. vm_compute. reflexivity. Qed.

Theorem q0_raw11_checkpoint_refines_parent :
  Forall
    (fun x => is_child_of (tm x) q32_canonical_residual_7)
    (fst q0_raw11_queue ++ snd q0_raw11_queue).
Proof.
  apply Forall_forall. intros x Hx.
  apply (proj1 (q32_source_refinesb_spec (tm x) q32_canonical_residual_7)).
  pose proof q0_raw11_refinesb_true as Htrue.
  unfold q0_raw11_refinesb in Htrue.
  apply forallb_forall with (x := x) in Htrue; [exact Htrue | exact Hx].
Qed.

Print Assumptions q0_raw11_refinesb_true.
Print Assumptions q0_raw11_checkpoint_counts.
Print Assumptions q0_raw11_checkpoint_refines_parent.
