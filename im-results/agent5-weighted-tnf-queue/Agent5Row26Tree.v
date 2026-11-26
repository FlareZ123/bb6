From BusyCoq Require Export Agent5CoarseTree Agent5Q0Solid26.
From Coq Require Import List Bool Arith Strings.String.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Inductive row26_tree : Type :=
| R26bad
| R26coarse (t : coarse_tree)
| R26solid
| R26split (n:nat) (h:Q*Sym) (kids:source_move -> row26_tree).

Fixpoint row26_check bound p t : bool :=
  match t with
  | R26bad => false
  | R26coarse c => coarse_check bound p c
  | R26solid => source_refinesb p solid26_tm
  | R26split n h kids => andb (Nat.leb (n+6) bound)
      (andb (source_hole_atb p n h)
        (forallb (fun v => row26_check bound (tm_upd p h v) (kids v)) source_moves))
  end.

Theorem row26_check_sound bound p t :
  row26_check bound p t = true -> source_table_safe bound p.
Proof.
  revert p.
  induction t as [|c| |n h kids IH]; intros p H; cbn [row26_check] in H.
  - discriminate.
  - eapply coarse_check_sound; exact H.
  - eapply source_table_safe_refine.
    + apply source_refinesb_spec. exact H.
    + apply solid26_safe.
  - rewrite !andb_true_iff in H. destruct H as [Hbound [Htrace Hkids]].
    eapply source_first_hole_split.
    + apply source_hole_atb_sound. exact Htrace.
    + apply Nat.leb_le. exact Hbound.
    + intro v. apply (IH v). apply forallb_forall with (x:=v) in Hkids.
      * exact Hkids.
      * apply source_moves_complete.
Qed.

Definition row26_split n h xs :=
  R26split n h (fun v => nth (source_move_index v) xs R26bad).

Print Assumptions row26_check_sound.
