From BusyCoq Require Import Enumerate62 Individual62 Agent8AdaptiveSource
  Agent8WeightedSource Agent47SourceWitness Agent47SourceChunk2 Agent47SourceTree
  Agent8Chunk2FirstHole Agent44Q32CanonicalParent Agent44ChunkSideSearch
  SourceResidualRoster.
From Coq Require Import List Bool Lia Arith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.
Open Scope nat_scope.

(* A direct source-tree closure attempt for canonical residual 7 (the q32
   parent). Its first undefined row is A1 after three moves. For each of the
   24 ordinary completions, prefer a checked translated-cycle certificate;
   otherwise split at the first undefined row reached within 18 moves. *)

Definition agent50_q32_child_tree (p : TM) : source_tree :=
  match find_side_candidate p with
  | Some c => STcert (candidate_witness c)
  | None => chunk2_first_hole_tree p
  end.

Definition agent50_q32_parent_tree : source_tree :=
  STsplit 3 (A,S1)
    (fun v => agent50_q32_child_tree
      (tm_upd q32_canonical_residual_7 (A,S1) v)).

Definition agent50_q32_parent_open : list TM :=
  source_tree_open q32_canonical_residual_7 agent50_q32_parent_tree.

Theorem agent50_q32_parent_tree_checked :
  source_tree_check 7014 q32_canonical_residual_7
    agent50_q32_parent_tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Theorem agent50_q32_parent_tree_open_count :
  length agent50_q32_parent_open =
    length (source_tree_open q32_canonical_residual_7 agent50_q32_parent_tree).
Proof. reflexivity. Qed.

(* Existing original-source certificates from the 34-node chunk roster and
   the newly searched 50-node side roster may cover some open leaves. *)
Definition agent50_q32_existing_roster : list TM :=
  chunk_roster ++ searched_chunk_roster.

Theorem agent50_q32_existing_roster_safe bound :
  Forall (source_table_safe bound) agent50_q32_existing_roster.
Proof.
  unfold agent50_q32_existing_roster.
  apply Forall_app. split.
  - apply chunk_roster_safe.
  - apply searched_chunk_roster_safe.
Qed.

Definition agent50_q32_roster_covers_tm (roster : list TM) (child : TM) : bool :=
  existsb (fun parent => source_refinesb child parent) roster.

Theorem agent50_q32_roster_covers_tm_sound bound roster child :
  Forall (source_table_safe bound) roster ->
  agent50_q32_roster_covers_tm roster child = true ->
  source_table_safe bound child.
Proof.
  intros Hroster Hcover.
  unfold agent50_q32_roster_covers_tm in Hcover.
  apply existsb_exists in Hcover.
  destruct Hcover as [parent [Hparent Href]].
  apply Forall_forall with (x:=parent) in Hroster; [|exact Hparent].
  eapply source_table_safe_refine.
  - apply source_refinesb_spec. exact Href.
  - exact Hroster.
Qed.

Definition agent50_q32_parent_open_uncovered : list TM :=
  filter
    (fun child => negb (agent50_q32_roster_covers_tm
      agent50_q32_existing_roster child))
    agent50_q32_parent_open.

Theorem agent50_q32_parent_open_uncovered_sound bound :
  Forall (source_table_safe bound) agent50_q32_parent_open_uncovered ->
  Forall (source_table_safe bound) agent50_q32_parent_open.
Proof.
  intro Hremaining.
  rewrite Forall_forall in Hremaining |- *.
  intros child Hchild.
  destruct (agent50_q32_roster_covers_tm
    agent50_q32_existing_roster child) eqn:E.
  - eapply agent50_q32_roster_covers_tm_sound.
    + apply agent50_q32_existing_roster_safe.
    + exact E.
  - apply Hremaining. unfold agent50_q32_parent_open_uncovered.
    apply filter_In. split; [exact Hchild|].
    unfold negb. now rewrite E.
Qed.

Theorem agent50_q32_parent_safe_from_open_uncovered :
  Forall (source_table_safe 7014) agent50_q32_parent_open_uncovered ->
  source_table_safe 7014 q32_canonical_residual_7.
Proof.
  intro Hremaining.
  eapply source_tree_sound.
  - exact agent50_q32_parent_tree_checked.
  - apply agent50_q32_parent_open_uncovered_sound. exact Hremaining.
Qed.

(* Exact finite frontier and a small traceable sample of remaining tables. *)
Time Eval vm_compute in
  (length agent50_q32_parent_open,
   length agent50_q32_parent_open_uncovered,
   firstn 12 (map TM_to_str agent50_q32_parent_open_uncovered)).

Print Assumptions agent50_q32_parent_tree_checked.
Print Assumptions agent50_q32_existing_roster_safe.
Print Assumptions agent50_q32_parent_safe_from_open_uncovered.
