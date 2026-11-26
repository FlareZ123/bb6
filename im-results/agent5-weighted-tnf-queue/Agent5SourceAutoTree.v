From BusyCoq Require Export Agent47SourceTree Agent47SourceWitness SourceResidualRoster Individual62 Agent5SourceAutomata.
From BusyCoq Require Import Enumerate62 Agent8WeightedSource.
From Coq Require Import List Bool Arith Lia.
Import ListNotations TNF_Node.
Open Scope nat_scope.

Inductive source_auto_tree : Type :=
| SATbad
| SATw (w:source_witness)
| SATcert (c:auto_cert)
| SATsplit (n:nat) (h:Q*Sym) (kids:source_move->source_auto_tree).

Fixpoint source_auto_check bound p (t:source_auto_tree) : bool :=
 match t with
 | SATbad => false
 | SATw w => source_witness_check bound p w
 | SATcert c => auto_cert_check p c
 | SATsplit n h kids => andb (Nat.leb (n+6) bound)
    (andb (source_hole_atb p n h)
       (forallb (fun v=>source_auto_check bound (tm_upd p h v) (kids v)) source_moves))
 end.

Theorem source_auto_check_sound bound p t :
 source_auto_check bound p t = true -> source_table_safe bound p.
Proof.
 revert p.
 induction t as [|w|c|n h kids IH]; intros p H; cbn [source_auto_check] in H.
 - discriminate.
 - eapply source_witness_check_sound; exact H.
 - apply source_nonhalt_cylinder. eapply auto_cert_nonhalt. exact H.
 - rewrite !andb_true_iff in H. destruct H as [Hbound [Htrace Hkids]].
   eapply source_first_hole_split.
   + apply source_hole_atb_sound. exact Htrace.
   + apply Nat.leb_le. exact Hbound.
   + intro v. apply (IH v). apply forallb_forall with (x:=v) in Hkids.
     * exact Hkids.
     * apply source_moves_complete.
Qed.

Definition source_auto_split n h xs :=
 SATsplit n h (fun v=>nth (source_move_index v) xs SATbad).
Print Assumptions source_auto_check_sound.
