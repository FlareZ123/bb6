From BusyCoq Require Import Enumerate62 Agent8AdaptiveSource Agent8GlobalSource Agent8WeightedSource
  Agent8SourceWF Individual62 Eqb.
From Coq Require Import List Bool Lia NArith.
Import ListNotations.
Import TNF_Node.

(* None is an unassigned row in a source cylinder. A certified parent
   can cover a more refined residual without exact table equality. *)
Definition source_table_safe (bound : nat) (p : TM) : Prop :=
  forall m, is_child_of m p -> weighted_bound bound m.

Definition source_refinesb (child parent : TM) : bool :=
  forallb (fun q => forallb (fun s =>
    match parent (q,s) with
    | None => true
    | Some v => BusyCoq.Eqb.eqb (child (q,s)) (Some v)
    end) all_syms) all_qs.

Theorem source_refinesb_spec child parent :
  source_refinesb child parent = true <-> is_child_of child parent.
Proof.
  unfold source_refinesb.
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

Theorem source_table_safe_refine bound child parent :
  is_child_of child parent ->
  source_table_safe bound parent ->
  source_table_safe bound child.
Proof.
  intros Href Hsafe m Hm.
  apply Hsafe. eapply child_trans; eassumption.
Qed.

Theorem source_nonhalt_cylinder bound p :
  ~ halts p c0 -> source_table_safe bound p.
Proof.
  intros Hnonhalt m Hm n k start Hn Hz Hk.
  exfalso. apply (child_nonhalt m p c0 Hm Hnonhalt).
  exists n. exact Hn.
Qed.

(* Last-hole trace: all ordinary fills are total tables; the halt fill
   has the recorded raw time. Charge <=5 incoming zero writes + query. *)
Theorem source_last_hole_cylinder bound p n h :
  get_num_undef_trans p = 1%nat ->
  halts_at p c0 n h ->
  (n + 6 <= bound)%nat ->
  source_table_safe bound p.
Proof.
  intros Hcount Htrace Hbound m Hchild k d start Hk Hz Hd.
  destruct h as [q s].
  inversion Htrace as [t c nn q' l s' r Hrun Hhole]; subst.
  destruct (m (q,s)) as [v|] eqn:Eact.
  - exfalso. apply (source_total_nonhalt m); [|exists k; exact Hk].
    intros g Hnone.
    destruct (BusyCoq.Eqb.eqb_spec g (q,s)) as [E|E].
    + subst g. congruence.
    + pose proof (source_count_one p (q,s) Hcount Hhole g E) as Hother.
      destruct (Hchild g); congruence.
  - assert (Hnm : halts_in m c0 n).
    { exists (q,(l,s,r)). split.
      - eapply child_multistep; eassumption.
      - exact Eact. }
    pose proof (source_time_unique m c0 k n Hk Hnm). lia.
Qed.

Definition source_roster_covers (roster : list TM) (x : T) : bool :=
  existsb (fun p => source_refinesb (tm x) p) roster.

Theorem source_roster_safe bound roster x :
  Forall (source_table_safe bound) roster ->
  source_roster_covers roster x = true ->
  source_weighted_safe bound x.
Proof.
  intros Hroster Hcover Hgood.
  apply existsb_exists in Hcover.
  destruct Hcover as [p [Hp Href]].
  apply Forall_forall with (x:=p) in Hroster; [|exact Hp].
  eapply source_table_safe_refine.
  - apply source_refinesb_spec. exact Href.
  - exact Hroster.
Qed.

Theorem source_obligations_from_roster bound roster nodes :
  Forall (source_table_safe bound) roster ->
  forallb (source_roster_covers roster) nodes = true ->
  Forall (source_weighted_safe bound) nodes.
Proof.
  intros Hroster Hcovered.
  apply Forall_forall. intros x Hx.
  eapply source_roster_safe; [exact Hroster|].
  apply forallb_forall with (x:=x) in Hcovered; assumption.
Qed.

Theorem actual_source_global_upper_from_roster bound plan roster :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) roster ->
  forallb (source_roster_covers roster)
    (adaptive_obligations decider plan q_0) = true ->
  forall t : TM, forall n, halts_in t c0 n -> S n <= bound.
Proof.
  intros Hmargin Hroster Hcovered.
  apply (actual_source_global_upper bound plan Hmargin).
  eapply source_obligations_from_roster; eassumption.
Qed.

Print Assumptions source_refinesb_spec.
Print Assumptions source_nonhalt_cylinder.
Print Assumptions source_last_hole_cylinder.
Print Assumptions source_obligations_from_roster.
Print Assumptions actual_source_global_upper_from_roster.
