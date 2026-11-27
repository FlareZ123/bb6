From BusyCoq Require Import Enumerate62 Eqb Individual62 Agent8QueueCheckpoint
  Agent8PackedChunk Agent32SourceEncoding Agent44Q32CanonicalParent.
From Coq Require Import List Bool Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.

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
  (List.length (fst q0_raw11_queue), List.length (snd q0_raw11_queue)) = (156%nat, 1%nat).
Proof. vm_compute. reflexivity. Qed.

Definition q0_raw11_tables : list string :=
  List.map (fun x => TM_to_str (tm x))
    (fst q0_raw11_queue ++ snd q0_raw11_queue).

Definition q0_raw11_tail_indices : list nat :=
  [136; 137; 138; 139; 140; 141; 142; 143;
   144; 145; 146; 147; 152; 153; 154; 155].

Definition q0_raw11_tail_tables : list string :=
  List.map (fun i => nth i q0_raw11_tables EmptyString) q0_raw11_tail_indices.

Definition q0_raw11_tail_expected : list string := [
  "1RB1LC_1RC---_0LA0LA_------_------_------";
  "1RB1LC_1RC---_0LA0RA_------_------_------";
  "1RB1LC_1RC---_0LA1LA_------_------_------";
  "1RB1LC_1RC---_0LA1RA_------_------_------";
  "1RB1LC_1RC---_0LA0LB_------_------_------";
  "1RB1LC_1RC---_0LA0RB_------_------_------";
  "1RB1LC_1RC---_0LA1LB_------_------_------";
  "1RB1LC_1RC---_0LA1RB_------_------_------";
  "1RB1LC_1RC---_0LA0LC_------_------_------";
  "1RB1LC_1RC---_0LA0RC_------_------_------";
  "1RB1LC_1RC---_0LA1LC_------_------_------";
  "1RB1LC_1RC---_0LA1RC_------_------_------";
  "1RB0LC_1RC---_0LA0LA_------_------_------";
  "1RB0LC_1RC---_0LA0RA_------_------_------";
  "1RB0LC_1RC---_0LA1LA_------_------_------";
  "1RB0LC_1RC---_0LA1RA_------_------_------"
].

Theorem q0_raw11_tail_tables_exact :
  q0_raw11_tail_tables = q0_raw11_tail_expected.
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
Print Assumptions q0_raw11_tail_tables_exact.
