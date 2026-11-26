From BusyCoq Require Import Agent5CoarseTree Agent5Q0Solid28.
From Coq Require Import List Bool Arith Strings.String.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

(* A checked coarse subtree or the explicitly proved unbounded sweep.
   Every split checks all 24 ordinary children and the halt sibling. *)
Inductive row28_tree : Type :=
| R28bad
| R28coarse (t : coarse_tree)
| R28solid
| R28split (n:nat) (h:Q*Sym) (kids:source_move -> row28_tree).

Fixpoint row28_check bound p t : bool :=
  match t with
  | R28bad => false
  | R28coarse c => coarse_check bound p c
  | R28solid => source_refinesb p solid28_tm
  | R28split n h kids => andb (Nat.leb (n+6) bound)
      (andb (source_hole_atb p n h)
        (forallb (fun v => row28_check bound (tm_upd p h v) (kids v)) source_moves))
  end.

Theorem row28_check_sound bound p t :
  row28_check bound p t = true -> source_table_safe bound p.
Proof.
  revert p.
  induction t as [|c| |n h kids IH]; intros p H; cbn [row28_check] in H.
  - discriminate.
  - eapply coarse_check_sound; exact H.
  - eapply source_table_safe_refine.
    + apply source_refinesb_spec. exact H.
    + apply solid28_safe.
  - rewrite !andb_true_iff in H. destruct H as [Hbound [Htrace Hkids]].
    eapply source_first_hole_split.
    + apply source_hole_atb_sound. exact Htrace.
    + apply Nat.leb_le. exact Hbound.
    + intro v. apply (IH v). apply forallb_forall with (x:=v) in Hkids.
      * exact Hkids.
      * apply source_moves_complete.
Qed.

Definition row28_split n h xs :=
  R28split n h (fun v => nth (source_move_index v) xs R28bad).

Print Assumptions row28_check_sound.
