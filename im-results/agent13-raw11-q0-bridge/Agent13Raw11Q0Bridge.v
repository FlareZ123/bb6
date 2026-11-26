From BusyCoq Require Import Agent47Raw11RestrictedQ0 Agent47Q0NineParentMembership
  Agent8WeightedSource Agent8SourceWF SourceResidualRoster Agent8PackedChunk.
From Coq Require Import List Lia.
Import ListNotations TNF_Node.
Open Scope nat_scope.

(* The Raw11 restriction and the nine-parent checkpoint roster are two
   views of the same finite frontier.  Keep this computation explicit:
   it is the reverse-coverage edge needed before parent safety can flow
   back through the two BFS rounds. *)
Lemma raw11_q0_active_covered_by_nine :
  forallb (source_roster_covers q0_nine_parent_roster)
    (fst raw11_q0_restriction) = true.
Proof.
  unfold raw11_q0_restriction.
  rewrite <- Agent8PackedChunk.chunk_data_exact.
  vm_compute.
Qed.

Lemma raw11_q0_held_covered_by_nine :
  forallb (source_roster_covers q0_nine_parent_roster)
    (snd raw11_q0_restriction) = true.
Proof.
  unfold raw11_q0_restriction.
  rewrite <- Agent8PackedChunk.chunk_data_exact.
  vm_compute.
Qed.

Lemma source_table_safe_mono lo hi p :
  lo <= hi ->
  source_table_safe lo p ->
  source_table_safe hi p.
Proof.
  unfold source_table_safe, weighted_bound.
  intros Hle Hsafe m Hchild n k s Hhalt Hz Hk.
  specialize (Hsafe m Hchild n k s Hhalt Hz Hk).
  lia.
Qed.

Lemma q0_nine_parent_roster_safe_1000006 :
  Forall (source_table_safe 234) q0_nine_parent_roster ->
  Forall (source_table_safe 1000006) q0_nine_parent_roster.
Proof.
  intros Hsmall.
  apply Forall_forall. intros p Hp.
  eapply source_table_safe_mono; [lia|].
  apply Forall_forall with (x:=p) in Hsmall; assumption.
Qed.

Lemma raw11_q0_restriction_safe_from_nine_parents :
  Forall (source_table_safe 1000006) q0_nine_parent_roster ->
  safeQ (source_weighted_safe 1000006) raw11_q0_restriction.
Proof.
  intro Hparents. unfold safeQ. split.
  - eapply source_obligations_from_roster; [exact Hparents|].
    exact raw11_q0_active_covered_by_nine.
  - eapply source_obligations_from_roster; [exact Hparents|].
    exact raw11_q0_held_covered_by_nine.
Qed.

Lemma raw11_node_source_good : source_good raw11_node.
Proof.
  unfold source_good, source_support.
  split; [cbn [raw11_node min_unused_state]; lia|].
  split; [reflexivity|].
  split; [reflexivity|].
  intros q s w d q' H.
  destruct q,s; cbn [raw11_node tm raw11_parent TM_from_str] in H;
    try discriminate; inversion H; subst;
    cbn [state_index raw11_node min_unused_state]; lia.
Qed.

(* The q0 decider has a 1,000,000-step horizon.  Lifting the nine parent
   bounds from 162 to 1,000,006 supplies the exact n+6 margin required by
   the source-local backwards theorem, while remaining below the global
   Canonical64 score floor. *)
Theorem raw11_parent_source_cover_1000006 :
  Forall (source_table_safe 234) q0_nine_parent_roster ->
  source_table_safe 1000006 raw11_parent.
Proof.
  intros Hparents.
  pose proof (q0_nine_parent_roster_safe_1000006 Hparents) as Hlarge.
  pose proof (source_weighted_local 1000006 ltac:(lia)) as Hlocal.
  pose proof
    (raw11_safe_from_restricted_q0 (source_weighted_safe 1000006)
      Hlocal (raw11_q0_restriction_safe_from_nine_parents Hlarge))
    as Hraw11.
  unfold source_table_safe.
  intros m Hchild.
  exact (Hraw11 raw11_node_source_good m Hchild).
Qed.

Print Assumptions raw11_parent_source_cover_1000006.
