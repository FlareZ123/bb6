From BusyCoq Require Import Enumerate62 Agent8QueueCheckpoint.
From Coq Require Import List NArith.
Import ListNotations.
Import TNF_Node.

Definition packed_slice (offset size : nat) (p : packed_queue) : packed_queue :=
  (firstn size (skipn offset (fst p)), snd p).

Lemma checkpoint_map_firstn {A B : Type} (f : A -> B) n xs :
  List.map f (firstn n xs) = firstn n (List.map f xs).
Proof.
  revert xs. induction n as [|n IH]; intros [|x xs]; cbn;
    try reflexivity. now rewrite IH.
Qed.

Lemma checkpoint_map_skipn {A B : Type} (f : A -> B) n xs :
  List.map f (skipn n xs) = skipn n (List.map f xs).
Proof.
  revert xs. induction n as [|n IH]; intros [|x xs]; cbn;
    try reflexivity. apply IH.
Qed.

Lemma decode_packed_slice offset size p :
  decode_queue (packed_slice offset size p) =
  (firstn size (skipn offset (fst (decode_queue p))), snd (decode_queue p)).
Proof.
  destruct p as [a b].
  unfold decode_queue, packed_slice. cbn [fst snd].
  rewrite checkpoint_map_firstn, checkpoint_map_skipn. reflexivity.
Qed.

Theorem source_root_checkpoint_decode p :
  encode_queue q_0 = p -> q_0 = decode_queue p.
Proof.
  intro E. rewrite <- E. symmetry.
  apply checkpoint_queue_roundtrip, checkpoint_q0_canonical.
Qed.

Theorem source_chunk_from_packed offset size p :
  encode_queue q_0 = p ->
  q_i offset size = decode_queue (packed_slice offset size p).
Proof.
  intro E. unfold q_i.
  rewrite (source_root_checkpoint_decode p E).
  symmetry. apply decode_packed_slice.
Qed.

Print Assumptions decode_packed_slice.
Print Assumptions source_root_checkpoint_decode.
Print Assumptions source_chunk_from_packed.
