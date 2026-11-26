From BusyCoq Require Import Enumerate62 Individual62 TC62 CTL62 Eqb.
From Coq Require Import List Bool NArith Lia Strings.String.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Open Scope string_scope.

(* Raw45 is a seven-hole D1 sibling of the authentic A0=1RB source root.
   The pinned q_0 is the four-round first-hole frontier.  Since q_0 nodes
   fix a different set of four slots, the relevant restriction is cylinder
   compatibility (intersection), not child/refinement. *)
Definition raw45_parent : TM :=
  TM_from_str "1RB---_1RC---_0RD---_1LD1RB_------_------".
Definition raw45_node : T := Build_T raw45_parent 7 4.

(* SourceResidualRoster.v's source_refinesb, retained here as the strict
   refinement predicate for comparisons and its source-semantic spec. *)
Definition raw45_source_refinesb (child parent : TM) : bool :=
  forallb (fun q => forallb (fun s =>
    match parent (q,s) with
    | None => true
    | Some v => BusyCoq.Eqb.eqb (child (q,s)) (Some v)
    end) all_syms) all_qs.

Theorem raw45_source_refinesb_spec child parent :
  raw45_source_refinesb child parent = true <-> is_child_of child parent.
Proof.
  unfold raw45_source_refinesb.
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

(* Two partial transition tables intersect exactly when no slot is assigned
   two different moves.  This is the cylinder-overlap relation needed to
   restrict the q_0 partition to Raw45. *)
Definition raw45_compatibleb (left right : TM) : bool :=
  forallb (fun q => forallb (fun s =>
    match left (q,s), right (q,s) with
    | Some a, Some b => BusyCoq.Eqb.eqb (Some a) (Some b)
    | _, _ => true
    end) all_syms) all_qs.

Definition raw45_compatible (left right : TM) : Prop :=
  forall q s, match left (q,s), right (q,s) with
    | Some a, Some b => a = b
    | _, _ => True
    end.

Theorem raw45_compatibleb_spec left right :
  raw45_compatibleb left right = true <-> raw45_compatible left right.
Proof.
  unfold raw45_compatibleb, raw45_compatible.
  split.
  - intros H q s.
    apply forallb_forall with (x:=q) in H; [|apply all_qs_spec].
    apply forallb_forall with (x:=s) in H; [|apply all_syms_spec].
    destruct (left (q,s)) as [a|], (right (q,s)) as [b|]; simpl in *; try exact I.
    destruct (BusyCoq.Eqb.eqb_spec (Some a) (Some b)); congruence.
  - intros H.
    apply forallb_forall. intros q _.
    apply forallb_forall. intros s _.
    destruct (left (q,s)) as [a|], (right (q,s)) as [b|]; simpl; try reflexivity.
    destruct (BusyCoq.Eqb.eqb_spec (Some a) (Some b)); [reflexivity|].
    exfalso. exact (H q s n).
Qed.

Definition raw45_q0_overlap : SearchQueue :=
  (filter (fun x => raw45_compatibleb (tm x) raw45_parent) (fst q_0),
   filter (fun x => raw45_compatibleb (tm x) raw45_parent) (snd q_0)).

Fixpoint raw45_collect_indices {A : Type} (p : A -> bool) (xs : list A)
    (n : nat) : list nat :=
  match xs with
  | [] => []
  | x :: rest =>
      if p x then n :: raw45_collect_indices p rest (S n)
      else raw45_collect_indices p rest (S n)
  end.

Definition raw45_q0_overlap_indices : list nat :=
  raw45_collect_indices
    (fun x => raw45_compatibleb (tm x) raw45_parent)
    (fst q_0) 0.

Definition raw45_q0_overlap_data : list (string * nat * nat) :=
  map (fun x => (TM_to_str (tm x), num_undef_trans x, min_unused_state x))
    (fst raw45_q0_overlap ++ snd raw45_q0_overlap).

Theorem raw45_node_metadata :
  raw45_node.(num_undef_trans) = 7 /\
  raw45_node.(min_unused_state) = 4.
Proof. split; reflexivity. Qed.

(* Exact bounded exports of the pinned q_0 list.  The indices identify the
   100-node q_i chunks that need no replay or, if absent, a targeted replay. *)
Eval vm_compute in
  (length (fst raw45_q0_overlap), length (snd raw45_q0_overlap)).
Eval vm_compute in raw45_q0_overlap_indices.
Eval vm_compute in raw45_q0_overlap_data.

Print Assumptions raw45_source_refinesb_spec.
Print Assumptions raw45_compatibleb_spec.
Print Assumptions raw45_node_metadata.
