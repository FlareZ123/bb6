From BusyCoq Require Import Agent50Q32ParentTreeSearch Agent44ChunkSideSearch
  Agent47SourceChunk2 SourceResidualRoster.
From Coq Require Import List Bool Lia Arith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* The parent source tree and the finite queue checkpoint are connected by
   a refinement cover, not by comparing their cardinalities. A parent-tree
   open leaf is discharged either by an original/new source certificate or
   by a surviving queue residual that it refines. *)

Definition q32_parent_combined_roster : list TM :=
  chunk_roster ++ searched_chunk_roster.

Definition q32_tm_roster_covers (roster : list TM) (p : TM) : bool :=
  existsb (fun parent => source_refinesb p parent) roster.

Definition q32_parent_open_covered_by_searched_chunkb : bool :=
  forallb
    (fun p =>
      q32_tm_roster_covers q32_parent_combined_roster p ||
      existsb (fun x => source_refinesb p (tm x)) searched_chunk_remaining)
    agent50_q32_parent_open_uncovered.

Definition q32_parent_open_uncovered_by_searched_chunk : list TM :=
  filter
    (fun p =>
      negb
        (q32_tm_roster_covers q32_parent_combined_roster p ||
         existsb (fun x => source_refinesb p (tm x)) searched_chunk_remaining))
    agent50_q32_parent_open_uncovered.

Time Eval vm_compute in
  (length agent50_q32_parent_open,
   length agent50_q32_parent_open_uncovered,
   length searched_chunk_remaining,
   q32_parent_open_covered_by_searched_chunkb,
   length q32_parent_open_uncovered_by_searched_chunk,
   firstn 12 (map TM_to_str q32_parent_open_uncovered_by_searched_chunk)).

Theorem q32_parent_combined_roster_safe bound :
  Forall (source_table_safe bound) q32_parent_combined_roster.
Proof.
  unfold q32_parent_combined_roster.
  rewrite Forall_app. split.
  - apply chunk_roster_safe.
  - apply searched_chunk_roster_safe.
Qed.

Theorem q32_parent_open_covered_by_searched_chunk_sound bound :
  q32_parent_open_covered_by_searched_chunkb = true ->
  Forall (source_table_safe bound) searched_chunk_remaining ->
  Forall (source_table_safe bound) agent50_q32_parent_open_uncovered.
Proof.
  intros Hcover Hremaining.
  apply Forall_forall. intros p Hp.
  unfold q32_parent_open_covered_by_searched_chunkb in Hcover.
  pose proof Hcover as Hall.
  apply forallb_forall with (x := p) in Hall; [|exact Hp].
  apply Bool.orb_true_iff in Hall.
  destruct Hall as [Hcert|Hrest].
  - unfold q32_tm_roster_covers in Hcert.
    apply existsb_exists in Hcert.
    destruct Hcert as [parent [Hparent Href]].
    pose proof (q32_parent_combined_roster_safe bound) as Hroster.
    apply Forall_forall with (x := parent) in Hroster; [|exact Hparent].
    eapply source_table_safe_refine.
    + apply source_refinesb_spec. exact Href.
    + exact Hroster.
  - apply existsb_exists in Hrest.
    destruct Hrest as [x [Hx Href]].
    apply Forall_forall with (x := x) in Hremaining; [|exact Hx].
    eapply source_table_safe_refine.
    + apply source_refinesb_spec. exact Href.
    + exact Hremaining.
Qed.

Theorem q32_parent_tree_checked_for_bound bound :
  24 <= bound ->
  source_tree_check bound q32_canonical_residual_7 agent50_q32_parent_tree = true.
Proof.
  intro Hbound.
  unfold agent50_q32_parent_tree.
  change
    (Nat.leb 9 bound &&
      (source_hole_atb q32_canonical_residual_7 3 (A,S1) &&
       forallb
         (fun v =>
           source_tree_check bound
             (tm_upd q32_canonical_residual_7 (A,S1) v)
             (agent50_bounded_source_tree 1
               (tm_upd q32_canonical_residual_7 (A,S1) v)))
         source_moves)) = true.
  apply andb_true_iff. split.
  - apply Nat.leb_le. lia.
  - apply andb_true_iff. split.
    + vm_compute. reflexivity.
    + apply forallb_forall. intros v Hv.
      apply agent50_bounded_source_tree_checked. exact Hbound.
Qed.

Theorem q32_parent_safe_from_searched_chunk_if_covered bound :
  24 <= bound ->
  q32_parent_open_covered_by_searched_chunkb = true ->
  Forall (source_table_safe bound) searched_chunk_remaining ->
  source_table_safe bound q32_canonical_residual_7.
Proof.
  intros Hbound Hcover Hremaining.
  eapply source_tree_sound.
  - apply q32_parent_tree_checked_for_bound. exact Hbound.
  - apply agent50_q32_parent_open_uncovered_sound.
    apply q32_parent_open_covered_by_searched_chunk_sound; assumption.
Qed.

Print Assumptions q32_parent_combined_roster_safe.
Print Assumptions q32_parent_open_covered_by_searched_chunk_sound.
Print Assumptions q32_parent_tree_checked_for_bound.
Print Assumptions q32_parent_safe_from_searched_chunk_if_covered.
