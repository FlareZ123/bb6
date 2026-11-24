From BusyCoq Require Import Enumerate62 Agent8QueueCheckpoint Agent8AdaptiveSource.
From Coq Require Import List NArith.
Import ListNotations.
Import TNF_Node.

(* One source update from a two-node slice, so the result is not drained. *)
Definition pilot_input := q_i 0 2.
Definition pilot_fuel : N := 1%N.
Time Definition pilot_data := Eval vm_compute in
  encode_queue (SearchQueue_upds decider pilot_input pilot_fuel).

Theorem pilot_checkpoint_exact :
  SearchQueue_upds decider pilot_input pilot_fuel =
  decode_queue pilot_data.
Proof.
  apply source_checkpoint_decode.
  - apply checkpoint_chunk_canonical.
  - vm_compute. reflexivity.
Qed.

Theorem pilot_remaining_active : fst (decode_queue pilot_data) <> [].
Proof. vm_compute. discriminate. Qed.

Time Definition pilot_resumed_data := Eval vm_compute in
  encode_queue (SearchQueue_upds decider (decode_queue pilot_data) 1%N).

Theorem pilot_resume_exact :
  SearchQueue_upds decider
    (SearchQueue_upds decider pilot_input pilot_fuel) 1%N =
  decode_queue pilot_resumed_data.
Proof.
  rewrite pilot_checkpoint_exact.
  apply source_checkpoint_decode.
  - rewrite <- pilot_checkpoint_exact.
    apply checkpoint_updates_canonical, checkpoint_chunk_canonical.
  - vm_compute. reflexivity.
Qed.

Print Assumptions pilot_checkpoint_exact.
Print Assumptions pilot_remaining_active.
Print Assumptions pilot_resume_exact.
Set Printing Width 120.
Print pilot_data.
Print pilot_resumed_data.
