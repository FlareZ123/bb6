From BusyCoq Require Import Agent47SourceChunk2 Individual62.
From Coq Require Import List Bool Arith.
Import ListNotations.
Import TNF_Node.

Definition q32_remaining_a1_class (p : TM) : nat :=
  match p (A,S1) with
  | Some (S1,L,D) => 0
  | Some (S1,R,D) => 1
  | None => 2
  | _ => 3
  end.

Time Eval vm_compute in
  (length (filter (fun p => Nat.eqb (q32_remaining_a1_class p) 0) chunk_remaining),
   length (filter (fun p => Nat.eqb (q32_remaining_a1_class p) 1) chunk_remaining),
   length (filter (fun p => Nat.eqb (q32_remaining_a1_class p) 2) chunk_remaining),
   length (filter (fun p => Nat.eqb (q32_remaining_a1_class p) 3) chunk_remaining)).
