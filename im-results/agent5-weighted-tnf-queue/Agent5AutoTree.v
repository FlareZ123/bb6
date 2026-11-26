From BusyCoq Require Export Agent5CoarseTree.
From BusyCoq Require Import Agent5Enumerate62DeciderSound CTL62 Individual62 Enumerate62.
From Coq Require Import List Bool Lia Arith NArith Strings.String.
Import ListNotations TNF_Node.
Open Scope nat_scope.

Definition auto_arg (l r : list N) :=
  MITMDFA 20000 80000 l r coarse_symbol_id (N_to_int 2).

Inductive auto_tree : Type :=
| ATbad
| ATcoarse (t : coarse_tree)
| ATdfa (l r : list N)
| ATsplit (n : nat) (h : Q*Sym) (kids : source_move -> auto_tree).

Fixpoint auto_check bound p t : bool :=
  match t with
  | ATbad => false
  | ATcoarse c => coarse_check bound p c
  | ATdfa l r => decide_nonhalt p (auto_arg l r)
  | ATsplit n h kids => andb (Nat.leb (n+6) bound)
       (andb (source_hole_atb p n h)
         (forallb (fun v => auto_check bound (tm_upd p h v) (kids v)) source_moves))
  end.

Theorem auto_check_sound bound p t :
  auto_check bound p t = true -> source_table_safe bound p.
Proof.
  revert p.
  induction t as [|c|l r|n h kids IH]; intros p H; cbn [auto_check] in H.
  - discriminate.
  - eapply coarse_check_sound; exact H.
  - apply source_nonhalt_cylinder. apply source_nonhalt_transfer.
    eapply agent5_decide_nonhalt_sound. exact H.
  - rewrite !andb_true_iff in H. destruct H as [Hbound [Htrace Hkids]].
    eapply source_first_hole_split.
    + apply source_hole_atb_sound. exact Htrace.
    + apply Nat.leb_le. exact Hbound.
    + intro v. apply (IH v). apply forallb_forall with (x:=v) in Hkids.
      * exact Hkids.
      * apply source_moves_complete.
Qed.

Definition auto_split n h xs :=
  ATsplit n h (fun v => nth (source_move_index v) xs ATbad).

Print Assumptions auto_check_sound.
