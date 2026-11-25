From BusyCoq Require Import Agent8Chunk2FirstHole Agent44ChunkSideSearch
  SourceResidualRoster.
From Coq Require Import List Bool Arith.
Import ListNotations.
Import TNF_Node.

(* The source queue's first side-search pass has already certified some of
   the 50 residuals. Refine only its genuinely uncovered nodes, rather than
   redundantly expanding all 50 into 1,200 children. *)

Fixpoint search_side_roster_tm (xs : list TM) : list source_certificate :=
  match xs with
  | [] => []
  | p :: rest =>
      match find_side_candidate (TM_from_str (TM_to_str p)) with
      | Some c =>
          (TM_to_str p, candidate_witness c) :: search_side_roster_tm rest
      | None => search_side_roster_tm rest
      end
  end.

Theorem search_side_roster_tm_checked bound xs :
  forallb (certificate_check bound) (search_side_roster_tm xs) = true.
Proof.
  induction xs as [|p xs IH]; cbn [search_side_roster_tm].
  - reflexivity.
  - destruct (find_side_candidate (TM_from_str (TM_to_str p))) as [c|]
      eqn:Hfind; cbn.
    + apply andb_true_intro. split.
      * apply source_certificate_check_of_candidate.
        apply find_side_candidate_sound. exact Hfind.
      * exact IH.
    + exact IH.
Qed.

Lemma searched_chunk_remaining_subset x :
  In x searched_chunk_remaining -> In x chunk_remaining.
Proof.
  unfold searched_chunk_remaining, source_uncovered.
  intro H.
  apply filter_In in H.
  exact (proj1 H).
Qed.

Definition searched_chunk_first_hole_children : list TM :=
  flat_map
    (fun x => source_tree_open (tm x) (chunk2_first_hole_tree (tm x)))
    searched_chunk_remaining.

Theorem searched_chunk_first_hole_tree_checks bound :
  24 <= bound ->
  forallb
    (fun x => source_tree_check bound (tm x) (chunk2_first_hole_tree (tm x)))
    searched_chunk_remaining = true.
Proof.
  intros Hbound.
  apply forallb_forall. intros x Hx.
  destruct (chunk2_first_hole_bound x
    (searched_chunk_remaining_subset x Hx)) as [n [h [Hfind Hn]]].
  eapply chunk2_first_hole_tree_check_of_find.
  - exact Hfind.
  - lia.
Qed.

Theorem searched_chunk_first_hole_frontier_sound bound :
  24 <= bound ->
  Forall (source_table_safe bound) searched_chunk_first_hole_children ->
  Forall (source_table_safe bound) searched_chunk_remaining.
Proof.
  intros Hbound Hchildren.
  apply Forall_forall. intros x Hx.
  assert (Hcheck :
    source_tree_check bound (tm x) (chunk2_first_hole_tree (tm x)) = true).
  { pose proof (searched_chunk_first_hole_tree_checks bound Hbound) as Hall.
    apply forallb_forall with (x := x) in Hall.
    - exact Hall.
    - exact Hx. }
  assert (Hopen :
    Forall (source_table_safe bound)
      (source_tree_open (tm x) (chunk2_first_hole_tree (tm x)))).
  { apply Forall_forall. intros p Hp.
    apply Forall_forall with (x := p) in Hchildren.
    - exact Hchildren.
    - unfold searched_chunk_first_hole_children.
      apply in_flat_map. exists x. split; assumption. }
  eapply source_tree_sound; eassumption.
Qed.

Definition searched_chunk_first_hole_side_certs :=
  search_side_roster_tm searched_chunk_first_hole_children.

Definition searched_chunk_first_hole_side_roster :=
  certificate_roster searched_chunk_first_hole_side_certs.

Definition source_roster_covers_tm (roster : list TM) (p : TM) : bool :=
  existsb (fun parent => source_refinesb p parent) roster.

Definition source_uncovered_tm (roster : list TM) (nodes : list TM) : list TM :=
  filter (fun p => negb (source_roster_covers_tm roster p)) nodes.

Theorem source_uncovered_tm_sound bound roster nodes :
  Forall (source_table_safe bound) roster ->
  Forall (source_table_safe bound) (source_uncovered_tm roster nodes) ->
  Forall (source_table_safe bound) nodes.
Proof.
  intros Hroster Hremaining.
  rewrite Forall_forall in Hremaining |- *.
  intros child Hchild.
  destruct (source_roster_covers_tm roster child) eqn:Hcover.
  - unfold source_roster_covers_tm in Hcover.
    apply existsb_exists in Hcover.
    destruct Hcover as [parent [Hparent Href]].
    apply Forall_forall with (x := parent) in Hroster; [|exact Hparent].
    eapply source_table_safe_refine.
    + apply source_refinesb_spec. exact Href.
    + exact Hroster.
  - apply Hremaining.
    unfold source_uncovered_tm.
    apply filter_In. split; [exact Hchild|].
    unfold negb. now rewrite Hcover.
Qed.

Definition searched_chunk_first_hole_side_remaining :=
  source_uncovered_tm searched_chunk_first_hole_side_roster
    searched_chunk_first_hole_children.

Theorem searched_chunk_first_hole_side_search_checked bound :
  forallb (certificate_check bound) searched_chunk_first_hole_side_certs = true.
Proof.
  unfold searched_chunk_first_hole_side_certs.
  apply search_side_roster_tm_checked.
Qed.

Theorem searched_chunk_first_hole_side_roster_safe bound :
  Forall (source_table_safe bound) searched_chunk_first_hole_side_roster.
Proof.
  unfold searched_chunk_first_hole_side_roster.
  apply certificate_roster_safe.
  apply searched_chunk_first_hole_side_search_checked.
Qed.

Theorem searched_chunk_first_hole_children_safe bound :
  Forall (source_table_safe bound) searched_chunk_first_hole_side_remaining ->
  Forall (source_table_safe bound) searched_chunk_first_hole_children.
Proof.
  intro Hremaining.
  eapply source_uncovered_tm_sound.
  - apply searched_chunk_first_hole_side_roster_safe.
  - exact Hremaining.
Qed.

Theorem searched_chunk_first_hole_remaining_safe bound :
  24 <= bound ->
  Forall (source_table_safe bound) searched_chunk_first_hole_side_remaining ->
  Forall (source_table_safe bound) searched_chunk_remaining.
Proof.
  intros Hbound Hremaining.
  apply searched_chunk_first_hole_frontier_sound.
  - exact Hbound.
  - apply searched_chunk_first_hole_children_safe. exact Hremaining.
Qed.

Theorem q32_queue_safe_from_first_hole_side_search bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) searched_chunk_first_hole_side_remaining ->
  safeQ (source_weighted_safe bound) (q_i 2 32).
Proof.
  intros Hbound Hremaining.
  apply chunk_initial_safe_of_search.
  - exact Hbound.
  - apply Forall_forall. intros x Hx.
    apply chunk2_source_table_safe_to_weighted.
    pose proof
      (searched_chunk_first_hole_remaining_safe bound (by lia) Hremaining)
      as Hparents.
    apply Forall_forall with (x := x) in Hparents.
    - exact Hparents.
    - exact Hx.
Qed.

Time Eval vm_compute in
  (length searched_chunk_remaining,
   length searched_chunk_first_hole_children,
   length searched_chunk_first_hole_side_certs,
   length searched_chunk_first_hole_side_remaining).
Time Eval vm_compute in (map fst searched_chunk_first_hole_side_certs).

Print Assumptions searched_chunk_first_hole_side_search_checked.
Print Assumptions searched_chunk_first_hole_side_roster_safe.
Print Assumptions searched_chunk_first_hole_children_safe.
Print Assumptions searched_chunk_first_hole_remaining_safe.
Print Assumptions q32_queue_safe_from_first_hole_side_search.
