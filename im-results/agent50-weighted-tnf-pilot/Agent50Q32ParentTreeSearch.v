From BusyCoq Require Import Enumerate62 Individual62 Agent8AdaptiveSource
  Agent8WeightedSource Agent47SourceWitness Agent47SourceChunk2 Agent47SourceTree
  Agent8Chunk2FirstHole Agent44Q32CanonicalParent Agent44ChunkSideSearch
  SourceResidualRoster.
From Coq Require Import List Bool Lia Arith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.
Open Scope nat_scope.

(* Search the exact table supplied to the source-tree checker. This
   deliberately avoids the string-roundtrip wrapper in Agent44's roster
   search, so the certificate check and tree check see the identical TM. *)
Definition agent50_find_side_candidate (p : TM) : option side_candidate :=
  find (side_candidate_check p) side_candidates.

(* A reusable bounded source-tree builder. At each node it prefers a
   checked translated-cycle certificate; otherwise it splits at the first
   undefined row reached within 18 moves, up to the requested depth. *)

Fixpoint agent50_bounded_source_tree (depth : nat) (p : TM) : source_tree :=
  match depth with
  | 0 => STopen
  | S d =>
      match agent50_find_side_candidate p with
      | Some c => STcert (candidate_witness c)
      | None =>
          match find_chunk2_hole p with
          | Some (n,h) =>
              STsplit n h
                (fun v => agent50_bounded_source_tree d (tm_upd p h v))
          | None => STopen
          end
      end
  end.

Definition agent50_q32_parent_tree : source_tree :=
  STsplit 3 (A,S1)
    (fun v => agent50_bounded_source_tree 1
      (tm_upd q32_canonical_residual_7 (A,S1) v)).

Lemma agent50_find_first_true {A : Type} (f : A -> bool) (xs : list A) (x : A) :
  find f xs = Some x -> f x = true.
Proof.
  induction xs as [|a xs IH]; cbn; intro H.
  - discriminate.
  - destruct (f a) eqn:Ha.
    + inversion H; subst. exact Ha.
    + eapply IH. exact H.
Qed.

Lemma agent50_find_side_candidate_sound p c :
  agent50_find_side_candidate p = Some c ->
  side_candidate_check p c = true.
Proof.
  unfold agent50_find_side_candidate.
  apply agent50_find_first_true.
Qed.

Lemma agent50_find_some_in {A : Type} (f : A -> bool) (xs : list A) (x : A) :
  find f xs = Some x -> In x xs.
Proof.
  induction xs as [|a xs IH]; cbn; intro H.
  - discriminate.
  - destruct (f a) eqn:Ha.
    + inversion H; subst. now left.
    + right. eapply IH. exact H.
Qed.

Lemma agent50_chunk2_hole_candidate_time_le18 n h :
  In (n,h) chunk2_hole_candidates -> n <= 18.
Proof.
  unfold chunk2_hole_candidates.
  intro Hin.
  apply in_flat_map in Hin.
  destruct Hin as [k [Hk Hin]].
  apply in_map_iff in Hin.
  destruct Hin as [h' [Heq Hh']].
  inversion Heq; subst n.
  apply in_seq in Hk. lia.
Qed.

Lemma agent50_find_chunk2_hole_time_le18 p n h :
  find_chunk2_hole p = Some (n,h) -> n <= 18.
Proof.
  intro Hfind.
  unfold find_chunk2_hole in Hfind.
  eapply agent50_chunk2_hole_candidate_time_le18.
  eapply agent50_find_some_in. exact Hfind.
Qed.

Lemma agent50_find_chunk2_hole_sound p n h :
  find_chunk2_hole p = Some (n,h) -> source_hole_atb p n h = true.
Proof.
  unfold find_chunk2_hole.
  apply agent50_find_first_true.
Qed.

Theorem agent50_bounded_source_tree_checked bound depth p :
  24 <= bound ->
  source_tree_check bound p (agent50_bounded_source_tree depth p) = true.
Proof.
  revert p.
  induction depth as [|d IH]; intros p Hbound.
  - reflexivity.
  - cbn [agent50_bounded_source_tree].
    destruct (find_side_candidate p) as [c|] eqn:Hside.
    + cbn [source_tree_check].
      pose proof (agent50_find_side_candidate_sound p c Hside) as Hcandidate.
      destruct c as [dir [entry [period budget]]].
      cbn [candidate_witness source_witness_check].
      unfold side_candidate_check in Hcandidate.
      exact Hcandidate.
    + destruct (find_chunk2_hole p) as [[n h]|] eqn:Hhole.
      * cbn [source_tree_check].
        apply andb_true_iff. split.
        -- apply Nat.leb_le.
           pose proof (agent50_find_chunk2_hole_time_le18 p n h Hhole).
           lia.
        -- apply andb_true_iff. split.
           ++ apply agent50_find_chunk2_hole_sound. exact Hhole.
           ++ apply forallb_forall. intros v Hv.
              apply IH. exact Hbound.
      * reflexivity.
Qed.

Definition agent50_q32_parent_open : list TM :=
  source_tree_open q32_canonical_residual_7 agent50_q32_parent_tree.

Theorem agent50_q32_parent_tree_checked :
  source_tree_check 7014 q32_canonical_residual_7
    agent50_q32_parent_tree = true.
Proof.
  unfold agent50_q32_parent_tree.
  change (Nat.leb 9 7014 &&
    (source_hole_atb q32_canonical_residual_7 3 (A,S1) &&
     forallb (fun v =>
       source_tree_check 7014
         (tm_upd q32_canonical_residual_7 (A,S1) v)
         (agent50_bounded_source_tree 1
           (tm_upd q32_canonical_residual_7 (A,S1) v)))
       source_moves)) = true.
  apply andb_true_iff. split.
  - vm_compute. reflexivity.
  - apply andb_true_iff. split.
    + vm_compute. reflexivity.
    + apply forallb_forall. intros v Hv.
      apply agent50_bounded_source_tree_checked. lia.
Qed.

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
