From BusyCoq Require Import Enumerate62 Individual62 TC62 CTL62 Eqb.
From Coq Require Import List Bool NArith Lia Strings.String.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Open Scope string_scope.

(* Raw45 is a seven-hole D1 sibling of the authentic A0=1RB source root.
   Its exact parent occurs in the pinned four-round q_0 source frontier. *)
Definition raw45_parent : TM :=
  TM_from_str "1RB---_1RC---_0RD---_1LD1RB_------_------".
Definition raw45_node : T := Build_T raw45_parent 7 4.

(* This is the source-native refinement executable used by
   SourceResidualRoster.v. *)
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

Definition raw45_q0_restriction : SearchQueue :=
  (filter (fun x => raw45_source_refinesb (tm x) raw45_parent) (fst q_0),
   filter (fun x => raw45_source_refinesb (tm x) raw45_parent) (snd q_0)).

Definition raw45_local_q0 : SearchQueue := ([raw45_node], []).

Fixpoint raw45_find_index {A : Type} (p : A -> bool) (xs : list A) : option nat :=
  match xs with
  | [] => None
  | x :: rest => if p x then Some 0 else option_map S (raw45_find_index p rest)
  end.

Definition raw45_q0_index : option nat :=
  raw45_find_index
    (fun x => raw45_source_refinesb (tm x) raw45_parent)
    (fst q_0).

Definition raw45_q0_match_data : list (string * nat * nat) :=
  map (fun x => (TM_to_str (tm x), num_undef_trans x, min_unused_state x))
    (fst raw45_q0_restriction ++ snd raw45_q0_restriction).

Theorem raw45_node_metadata :
  raw45_node.(num_undef_trans) = 7 /\
  raw45_node.(min_unused_state) = 4.
Proof. split; reflexivity. Qed.

(* The exact parent restriction, its position in q_0, and its canonical
   cached metadata are all checked by Coq's VM, not by an external parser. *)
Theorem raw45_q0_restriction_exact :
  raw45_q0_restriction = raw45_local_q0.
Proof. vm_compute. reflexivity. Qed.

Theorem raw45_q0_index_exact : raw45_q0_index = Some 1539.
Proof. vm_compute. reflexivity. Qed.

Theorem raw45_q0_nth :
  nth_error (fst q_0) 1539 = Some raw45_node.
Proof. vm_compute. reflexivity. Qed.

Eval vm_compute in raw45_q0_index.
Eval vm_compute in raw45_q0_match_data.

Print Assumptions raw45_source_refinesb_spec.
Print Assumptions raw45_node_metadata.
Print Assumptions raw45_q0_restriction_exact.
Print Assumptions raw45_q0_index_exact.
Print Assumptions raw45_q0_nth.
