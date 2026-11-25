From BusyCoq Require Import Agent44Q32CanonicalParent
  Agent5Enumerate62DeciderSound Agent47SourceTree SourceResidualRoster.
From Coq Require Import List Bool Arith Lia NArith.
Import ListNotations.
Import TNF_Node.

(* A decider-first source tree. Unlike the earlier 18-step first-hole
   search, every Halt verdict carries a formal <= 1,000,000-step trace.
   Split such cylinders completely; close NonHalt and one-hole halting
   cylinders directly; retain Unknown or depth-limited nodes as open. *)

Inductive q32_decider_tree : Type :=
| QDopen
| QDnonhalt
| QDlast
| QDsplit (h : Q * Sym) (children : source_move -> q32_decider_tree).

Fixpoint q32_decider_tree_of (depth : nat) (p : TM) : q32_decider_tree :=
  match decider p with
  | Halt h =>
      if Nat.eqb (get_num_undef_trans p) 1 then QDlast
      else
        match depth with
        | O => QDopen
        | S d => QDsplit h
            (fun v => q32_decider_tree_of d (tm_upd p h v))
        end
  | NonHalt => QDnonhalt
  | Unknown => QDopen
  end.

Fixpoint q32_decider_tree_open (p : TM) (t : q32_decider_tree) : list TM :=
  match t with
  | QDopen => [p]
  | QDnonhalt => []
  | QDlast => []
  | QDsplit h children =>
      flat_map
        (fun v => q32_decider_tree_open (tm_upd p h v) (children v))
        source_moves
  end.

Theorem q32_decider_tree_of_sound bound depth p :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound)
    (q32_decider_tree_open p (q32_decider_tree_of depth p)) ->
  source_table_safe bound p.
Proof.
  revert p.
  induction depth as [|d IH]; intros p Hbound Hopen.
  - unfold q32_decider_tree_of.
    destruct (decider p) as [h| |] eqn:Hdec.
    + destruct (Nat.eqb (get_num_undef_trans p) 1) eqn:Hone.
      * cbn [q32_decider_tree_open] in Hopen.
        pose proof (agent32_decider_bounded_sound p) as Hsound.
        rewrite Hdec in Hsound.
        destruct Hsound as [n [Hhalt Hn]].
        eapply source_last_hole_cylinder.
        -- apply Nat.eqb_eq. exact Hone.
        -- exact Hhalt.
        -- lia.
      * cbn [q32_decider_tree_open] in Hopen.
        inversion Hopen; assumption.
    + cbn [q32_decider_tree_open] in Hopen.
      pose proof (agent32_decider_bounded_sound p) as Hsound.
      rewrite Hdec in Hsound.
      eapply source_nonhalt_cylinder. exact Hsound.
    + cbn [q32_decider_tree_open] in Hopen.
      inversion Hopen; assumption.
  - unfold q32_decider_tree_of.
    destruct (decider p) as [h| |] eqn:Hdec.
    + destruct (Nat.eqb (get_num_undef_trans p) 1) eqn:Hone.
      * cbn [q32_decider_tree_open] in Hopen.
        pose proof (agent32_decider_bounded_sound p) as Hsound.
        rewrite Hdec in Hsound.
        destruct Hsound as [n [Hhalt Hn]].
        eapply source_last_hole_cylinder.
        -- apply Nat.eqb_eq. exact Hone.
        -- exact Hhalt.
        -- lia.
      * cbn [q32_decider_tree_open] in Hopen.
        pose proof (agent32_decider_bounded_sound p) as Hsound.
        rewrite Hdec in Hsound.
        destruct Hsound as [n [Hhalt Hn]].
        eapply source_first_hole_split.
        -- exact Hhalt.
        -- lia.
        -- intros v.
           apply IH.
           ++ exact Hbound.
           ++ apply Forall_forall. intros m Hm.
              apply Forall_forall with (x := m) in Hopen.
              ** exact Hopen.
              ** apply in_flat_map. exists v. split.
                 --- apply source_moves_complete.
                 --- exact Hm.
    + cbn [q32_decider_tree_open] in Hopen.
      pose proof (agent32_decider_bounded_sound p) as Hsound.
      rewrite Hdec in Hsound.
      eapply source_nonhalt_cylinder. exact Hsound.
    + cbn [q32_decider_tree_open] in Hopen.
      inversion Hopen; assumption.
Qed.

Definition q32_decider_tree_depth2 :=
  q32_decider_tree_of 2 q32_canonical_residual_7.

Definition q32_decider_tree_depth2_open :=
  q32_decider_tree_open q32_canonical_residual_7 q32_decider_tree_depth2.

Theorem q32_parent_safe_from_decider_tree_depth2 bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) q32_decider_tree_depth2_open ->
  source_table_safe bound q32_canonical_residual_7.
Proof.
  intros Hbound Hopen.
  eapply q32_decider_tree_of_sound.
  - exact Hbound.
  - exact Hopen.
Qed.

Time Eval vm_compute in
  (length q32_decider_tree_depth2_open,
   firstn 24 (map TM_to_str q32_decider_tree_depth2_open)).

Print Assumptions q32_decider_tree_of_sound.
Print Assumptions q32_parent_safe_from_decider_tree_depth2.
