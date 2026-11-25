From BusyCoq Require Import Agent8Chunk2FirstHole Agent44ChunkSideSearch.
From BusyCoq Require Import SourceResidualRoster.
From Coq Require Import List Bool Arith.
Import ListNotations.
Import TNF_Node.

(* The 1,200 grandchildren are a list of source TM tables, not TNF_Node
   queue records.  Keep the source-side certificate search and refinement
   relation at that exact type; do not pass them through the list-T adapter
   used by the earlier 50-node queue. *)

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

Definition chunk2_first_hole_side_certs :=
  search_side_roster_tm chunk2_first_hole_children.

Definition chunk2_first_hole_side_roster :=
  certificate_roster chunk2_first_hole_side_certs.

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

Definition chunk2_first_hole_side_remaining :=
  source_uncovered_tm chunk2_first_hole_side_roster chunk2_first_hole_children.

Theorem chunk2_first_hole_side_search_checked bound :
  forallb (certificate_check bound) chunk2_first_hole_side_certs = true.
Proof.
  unfold chunk2_first_hole_side_certs.
  apply search_side_roster_tm_checked.
Qed.

Theorem chunk2_first_hole_side_roster_safe bound :
  Forall (source_table_safe bound) chunk2_first_hole_side_roster.
Proof.
  unfold chunk2_first_hole_side_roster.
  apply certificate_roster_safe.
  apply chunk2_first_hole_side_search_checked.
Qed.

Theorem chunk2_first_hole_children_safe bound :
  Forall (source_table_safe bound) chunk2_first_hole_side_remaining ->
  Forall (source_table_safe bound) chunk2_first_hole_children.
Proof.
  apply source_uncovered_tm_sound.
  apply chunk2_first_hole_side_roster_safe.
Qed.

Theorem chunk2_first_hole_initial_safe_from_side_search bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) chunk2_first_hole_side_remaining ->
  safeQ (source_weighted_safe bound) (q_i 2 32).
Proof.
  intros Hbound Hremaining.
  apply chunk2_first_hole_initial_safe.
  - exact Hbound.
  - apply chunk2_first_hole_children_safe. exact Hremaining.
Qed.

Time Eval vm_compute in
  (length chunk2_first_hole_children,
   length chunk2_first_hole_side_certs,
   length chunk2_first_hole_side_remaining).
Time Eval vm_compute in (map fst chunk2_first_hole_side_certs).

Print Assumptions chunk2_first_hole_side_search_checked.
Print Assumptions chunk2_first_hole_side_roster_safe.
Print Assumptions chunk2_first_hole_children_safe.
Print Assumptions chunk2_first_hole_initial_safe_from_side_search.
