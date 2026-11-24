From BusyCoq Require Import Enumerate62 Individual62 Agent8QueueCheckpoint Agent8PackedRoot.
From Coq Require Import List NArith Strings.String Lia.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.

(* Select the first actual source Halt rather than guessing a range. *)
Fixpoint find_halt_index (xs : list T) (i : nat) : option nat :=
  match xs with
  | [] => None
  | x::rest =>
    match decider (tm x) with
    | Halt _ => Some i
    | _ => find_halt_index rest (S i)
    end
  end.

Time Definition expand_offset : nat := Eval vm_compute in
  match find_halt_index (fst q_0) O with
  | Some i => i | None => O
  end.

Definition expand_input := q_i expand_offset 2.
Time Definition expand_data := Eval vm_compute in
  encode_queue (SearchQueue_upds decider expand_input 1%N).

Theorem expand_checkpoint_exact :
  SearchQueue_upds decider expand_input 1%N = decode_queue expand_data.
Proof.
  apply source_checkpoint_decode.
  - apply checkpoint_chunk_canonical.
  - vm_compute. reflexivity.
Qed.

Theorem expand_created_children :
  (2 < List.length (fst (decode_queue expand_data)))%nat.
Proof. vm_compute. lia. Qed.

Time Definition expand_resume_data := Eval vm_compute in
  encode_queue (SearchQueue_upds decider (decode_queue expand_data) 1%N).

Theorem expand_resume_exact :
  SearchQueue_upds decider (SearchQueue_upds decider expand_input 1%N) 1%N =
  decode_queue expand_resume_data.
Proof.
  rewrite expand_checkpoint_exact.
  apply source_checkpoint_decode.
  - rewrite <- expand_checkpoint_exact.
    apply checkpoint_updates_canonical, checkpoint_chunk_canonical.
  - vm_compute. reflexivity.
Qed.

Print Assumptions expand_checkpoint_exact.
Print Assumptions expand_created_children.
Print Assumptions expand_resume_exact.
Set Printing Depth 10000.
Set Printing Width 120.
Print expand_offset.
Print expand_data.
Print expand_resume_data.
