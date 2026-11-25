From BusyCoq Require Export Agent47SourceTree Agent47SourceWitness SourceResidualRoster Individual62.
From BusyCoq Require Import Agent5Enumerate62DeciderSound CTL62 Individual62 Enumerate62 Agent8WeightedSource.
From Coq Require Import List Bool Lia Arith NArith Strings.String.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Definition coarse_symbol_id (s : Sym) := match s with S0 => int0 | S1 => int1 end.
Open Scope N_scope.
Definition coarse_dfa (k:nat) : list N :=
 match k with
 | 0%nat => [0; 1; 2; 1; 2; 1]
 | 1%nat => [0; 1; 2; 3; 2; 3; 2; 3]
 | 2%nat => [0; 1; 2; 3; 4; 5; 6; 7; 4; 5; 6; 7; 4; 5; 6; 7]
 | 3%nat => [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 8; 9; 10; 11; 12; 13; 14; 15; 8; 9; 10; 11; 12; 13; 14; 15]
 | 4%nat => [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]
 | 5%nat => [1; 2; 1; 2; 3; 4; 5; 2; 3; 2; 3; 2]
 | 6%nat => [1; 2; 1; 2; 3; 4; 5; 2; 3; 6; 7; 2; 3; 2; 3; 2]
 | 7%nat => [1; 2; 1; 2; 3; 4; 5; 2; 3; 6; 7; 2; 3; 8; 9; 2; 3; 2; 3; 2]
 | 8%nat => [1; 2; 1; 2; 3; 4; 5; 2; 3; 6; 7; 2; 3; 4; 5; 2]
 | 9%nat => [1; 2; 1; 2; 3; 4; 5; 2; 3; 6; 7; 2; 3; 8; 9; 2; 3; 4; 5; 2]
 | 10%nat => [1; 2; 1; 2; 3; 4; 5; 2; 3; 6; 7; 2; 3; 6; 7; 2]
 | 11%nat => [1; 2; 1; 2; 3; 4; 5; 6; 7; 4; 5; 8; 3; 9; 10; 6; 3; 11; 7; 9; 10; 8; 7; 11]
 | 12%nat => [1; 2; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 3; 11; 12; 6; 13; 8; 9; 14; 3; 15; 7; 16; 17; 10; 18; 6; 3; 19; 7; 20; 13; 16; 17; 14; 21; 10; 7; 22; 13; 20; 21; 14; 13; 22]
 | 13%nat => [1; 2; 1; 2; 3; 4; 5; 6; 7; 2; 3; 8; 3; 9; 10; 6; 3; 11; 7; 6; 7; 8; 7; 8]
 | 14%nat => [1; 2; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 3; 11; 12; 6; 13; 2; 3; 14; 3; 15; 7; 16; 17; 10; 18; 6; 3; 19; 7; 20; 13; 6; 7; 14; 21; 10; 7; 22; 13; 10; 13; 14; 13; 14]
 | 15%nat => [1; 2; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 3; 11; 12; 6; 13; 4; 5; 14; 3; 15; 7; 16; 17; 10; 18; 6; 3; 19; 7; 20; 13; 11; 12; 14; 21; 10; 7; 22; 13; 15; 18; 14; 13; 19]
 | 16%nat => [1; 2; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 3; 11; 12; 6; 13; 14; 15; 16; 3; 17; 7; 18; 19; 10; 20; 6; 21; 2; 3; 22; 3; 23; 7; 24; 13; 25; 26; 16; 27; 10; 28; 6; 3; 29; 7; 30; 13; 31; 21; 6; 7; 22; 32; 16; 33; 10; 7; 34; 13; 35; 21; 10; 13; 22; 36; 16; 13; 37; 21; 16; 21; 22; 21; 22]
 | 17%nat => [1; 2; 1; 2; 3; 4; 5; 6; 7; 2; 3; 8; 9; 10; 11; 12; 13; 14; 15; 6; 16; 6; 7; 17; 9; 18; 19; 6; 20; 8; 9; 8; 21; 12; 13; 22; 16; 12; 13; 8; 23; 12; 16; 17; 20; 17; 20; 17]
 | 18%nat => [1; 2; 1; 2; 3; 4; 5; 6; 7; 4; 5; 8; 9; 10; 11; 12; 13; 14; 15; 6; 16; 10; 11; 17; 9; 18; 19; 6; 20; 14; 15; 8; 21; 12; 13; 22; 16; 18; 19; 8; 23; 12; 21; 17; 20; 22; 23; 17]
 | 19%nat => [1; 2; 1; 2; 3; 4; 5; 2; 3; 6; 7; 2; 3; 8; 9; 2; 3; 6; 7; 2]
 | 20%nat => [1; 2; 1; 2; 3; 4; 5; 2; 3; 6; 7; 2; 3; 8; 9; 2; 3; 10; 11; 2; 3; 2; 3; 2]
 | 21%nat => [1; 2; 1; 2; 3; 4; 5; 2; 3; 6; 7; 2; 3; 8; 9; 2; 3; 10; 11; 2; 3; 12; 13; 2; 3; 2; 3; 2]
 | _ => []
 end.
Definition coarse_arg (k:nat) := MITMDFA 20000 80000 (coarse_dfa k) (coarse_dfa k) coarse_symbol_id (N_to_int 2).
Definition coarse_pair_arg (l r:nat) := MITMDFA 20000 80000 (coarse_dfa l) (coarse_dfa r) coarse_symbol_id (N_to_int 2).
Open Scope nat_scope.
Inductive coarse_tree : Type :=
| CTbad
| CTw (w:source_witness)
| CTmitm (k:nat)
| CTpair (l r:nat)
| CTsplit (n:nat) (h:Q*Sym) (kids:source_move->coarse_tree).
Fixpoint coarse_check bound p (t:coarse_tree) : bool :=
 match t with
 | CTbad => false
 | CTw w => source_witness_check bound p w
 | CTmitm k => decide_nonhalt p (coarse_arg k)
 | CTpair l r => decide_nonhalt p (coarse_pair_arg l r)
 | CTsplit n h kids => andb (Nat.leb (n+6) bound)
    (andb (source_hole_atb p n h)
       (forallb (fun v=>coarse_check bound (tm_upd p h v) (kids v)) source_moves))
 end.
Theorem coarse_check_sound bound p t : coarse_check bound p t = true -> source_table_safe bound p.
Proof.
 revert p.
 induction t as [|w|k|l r|n h kids IH]; intros p H; cbn [coarse_check] in H.
 - discriminate.
 - eapply source_witness_check_sound; exact H.
 - apply source_nonhalt_cylinder. apply source_nonhalt_transfer. eapply agent5_decide_nonhalt_sound. exact H.
 - apply source_nonhalt_cylinder. apply source_nonhalt_transfer. eapply agent5_decide_nonhalt_sound. exact H.
 - rewrite !andb_true_iff in H. destruct H as [Hbound [Htrace Hkids]].
   eapply source_first_hole_split.
   + apply source_hole_atb_sound. exact Htrace.
   + apply Nat.leb_le. exact Hbound.
   + intro v. apply (IH v). apply forallb_forall with (x:=v) in Hkids.
     * exact Hkids.
     * apply source_moves_complete.
Qed.
Definition coarse_split n h xs := CTsplit n h (fun v=>nth (source_move_index v) xs CTbad).
Definition coarse_certificate := (string*coarse_tree)%type.
Definition coarse_tm (c:coarse_certificate) := TM_from_str (fst c).
Definition coarse_candidate_check bound c := coarse_check bound (coarse_tm c) (snd c).
Theorem coarse_roster_safe bound cs :
 forallb (coarse_candidate_check bound) cs = true -> Forall (source_table_safe bound) (map coarse_tm cs).
Proof.
 induction cs as [|c cs IH]; cbn [forallb map].
 - intros _. constructor.
 - rewrite andb_true_iff. intros [HC HS]. constructor.
   + exact (coarse_check_sound bound (coarse_tm c) (snd c) HC).
   + apply IH. exact HS.
Qed.
Lemma coarse_roster_mono lo hi roster :
 lo <= hi -> Forall (source_table_safe lo) roster -> Forall (source_table_safe hi) roster.
Proof.
 intros Hle H. apply Forall_forall; intros p Hp.
 apply Forall_forall with (x:=p) in H; [|exact Hp].
 intros m Hm n k s Hn Hz Hk.
 pose proof (H m Hm n k s Hn Hz Hk). lia.
Qed.
Print Assumptions coarse_check_sound.
Print Assumptions coarse_roster_safe.
Print Assumptions coarse_roster_mono.
