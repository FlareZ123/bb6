From BusyCoq Require Import Enumerate62 Individual62 TC62 Agent8SourceWF
  Agent8QueueCheckpoint Agent8PackedChunk2_32_32 Agent32SourceEncoding
  Agent44Q32CanonicalParent.
From Coq Require Import List Bool Arith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* The canonical parent is itself a partial machine that reaches A1 after
   the fixed A0, B0, C0 prefix. Its first-hole split is therefore the
   relevant closure interface, not a nonhalting-side certificate. *)
Definition q32_parent_node : T :=
  Build_T (tm_simpl q32_canonical_residual_7) 9 3.

Definition q32_parent_decision :=
  decider (tm q32_parent_node).

Definition q32_parent_halt_slot : option (Q * Sym) :=
  match q32_parent_decision with
  | TC62.TM.Halt h => Some h
  | _ => None
  end.

Time Eval vm_compute in q32_parent_decision.
Theorem q32_parent_first_hole_is_A1 :
  q32_parent_halt_slot = Some (A,S1).
Proof. vm_compute. reflexivity. Qed.

Definition q32_parent_children : list T :=
  match q32_parent_decision with
  | TC62.TM.Halt h => expand' q32_parent_node h
  | _ => []
  end.

Definition q32_parent_child_coveredb (child : T) : bool :=
  existsb (fun x =>
    q32_source_refinesb (tm x) (tm child))
    (fst (decode_queue packed_chunk_2_32_32)).

Definition q32_parent_children_coveredb : bool :=
  forallb q32_parent_child_coveredb q32_parent_children.

Definition q32_parent_uncovered_children : list T :=
  filter (fun child => negb (q32_parent_child_coveredb child))
    q32_parent_children.

Time Eval vm_compute in
  (List.length q32_parent_children,
   q32_parent_children_coveredb,
   List.map (fun x => TM_to_str (tm x)) q32_parent_uncovered_children).

Definition q32_parent_child_class (x : T) : nat :=
  match decider (tm x) with
  | TC62.TM.Halt _ => 0
  | TC62.TM.NonHalt => 1
  | TC62.TM.Unknown => 2
  end.

Time Eval vm_compute in
  (map (fun x => (TM_to_str (tm x), q32_parent_child_class x))
    q32_parent_children).

Theorem q32_parent_children_covered :
  q32_parent_children_coveredb = true ->
  forall child, In child q32_parent_children ->
    exists x,
      In x (fst (decode_queue packed_chunk_2_32_32)) /\
      is_child_of (tm x) (tm child).
Proof.
  intros Hcovered child Hchild.
  unfold q32_parent_children_coveredb in Hcovered.
  apply forallb_forall with (x:=child) in Hcovered; [|exact Hchild].
  unfold q32_parent_child_coveredb in Hcovered.
  apply existsb_exists in Hcovered.
  destruct Hcovered as [x [Hx Href]].
  exists x. split; [exact Hx|].
  apply (proj1 (q32_source_refinesb_spec (tm x) (tm child))).
  exact Href.
Qed.

Theorem q32_parent_node_metadata :
  num_undef_trans q32_parent_node = 9 /\
  min_unused_state q32_parent_node = 3.
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions q32_parent_first_hole_is_A1.
Print Assumptions q32_parent_children_covered.
