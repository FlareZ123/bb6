From BusyCoq Require Import Agent8Chunk2FirstHole Agent44ChunkSideSearch
  Agent47SourceWitness SourceResidualRoster.
From Coq Require Import List Bool Lia Arith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.
Open Scope nat_scope.

(* Second-level source-side closure experiment. The first-hole theorem leaves
   1,200 ordinary children from the 50 q_i(2,32), fuel-32 residuals. Search
   those children with the pinned BusyCoq translated-cycler verifier. This
   first pass uses budget 0; any unmatched child remains explicit. *)

Definition agent50_child_side_candidates_zero : list side_candidate :=
  flat_map (fun d =>
    flat_map (fun entry =>
      map (fun period => (d,(entry,(period,0)))) (seq 1 13))
      (seq 0 13))
    [L;R].

Definition agent50_find_child_side_candidate (table_string : string) : option side_candidate :=
  find (side_candidate_check (TM_from_str table_string))
    agent50_child_side_candidates_zero.

Lemma agent50_find_first_true {A : Type} (f : A -> bool) (xs : list A) (x : A) :
  find f xs = Some x -> f x = true.
Proof.
  induction xs as [|a xs IH]; cbn; intro H.
  - discriminate.
  - destruct (f a) eqn:Ha.
    + inversion H; subst. exact Ha.
    + eapply IH. exact H.
Qed.

Lemma agent50_find_child_side_candidate_sound table_string c :
  agent50_find_child_side_candidate table_string = Some c ->
  side_candidate_check (TM_from_str table_string) c = true.
Proof.
  unfold agent50_find_child_side_candidate.
  apply agent50_find_first_true.
Qed.

Lemma agent50_source_certificate_check_of_candidate bound table_string c :
  side_candidate_check (TM_from_str table_string) c = true ->
  certificate_check bound (table_string, candidate_witness c) = true.
Proof.
  intro H.
  destruct c as [d [entry [period budget]]].
  unfold candidate_witness, certificate_check, certificate_tm,
    source_witness_check, side_candidate_check.
  cbn. exact H.
Qed.

Fixpoint agent50_search_child_side_roster
    (table_strings : list string) : list source_certificate :=
  match table_strings with
  | [] => []
  | table_string :: rest =>
      match agent50_find_child_side_candidate table_string with
      | Some c =>
          (table_string, candidate_witness c) ::
            agent50_search_child_side_roster rest
      | None => agent50_search_child_side_roster rest
      end
  end.

Theorem agent50_search_child_side_roster_checked bound xs :
  forallb (certificate_check bound) (agent50_search_child_side_roster xs) = true.
Proof.
  induction xs as [|table_string xs IH]; cbn [agent50_search_child_side_roster].
  - reflexivity.
  - destruct (agent50_find_child_side_candidate table_string) as [c|] eqn:Hfind; cbn.
    + apply andb_true_intro. split.
      * apply agent50_source_certificate_check_of_candidate.
        apply agent50_find_child_side_candidate_sound. exact Hfind.
      * exact IH.
    + exact IH.
Qed.

Definition agent50_child_side_strings : list string :=
  nodup string_dec (map TM_to_str chunk2_first_hole_children).

Definition agent50_child_side_certificates : list source_certificate :=
  agent50_search_child_side_roster agent50_child_side_strings.

Definition agent50_child_side_roster : list TM :=
  certificate_roster agent50_child_side_certificates.

Theorem agent50_child_side_roster_safe bound :
  Forall (source_table_safe bound) agent50_child_side_roster.
Proof.
  unfold agent50_child_side_roster, agent50_child_side_certificates.
  apply certificate_roster_safe.
  apply agent50_search_child_side_roster_checked.
Qed.

Definition agent50_source_roster_covers_tm (roster : list TM) (child : TM) : bool :=
  existsb (fun parent => source_refinesb child parent) roster.

Theorem agent50_source_roster_covers_tm_sound bound roster child :
  Forall (source_table_safe bound) roster ->
  agent50_source_roster_covers_tm roster child = true ->
  source_table_safe bound child.
Proof.
  intros Hroster Hcover.
  unfold agent50_source_roster_covers_tm in Hcover.
  apply existsb_exists in Hcover.
  destruct Hcover as [parent [Hparent Href]].
  apply Forall_forall with (x:=parent) in Hroster; [|exact Hparent].
  eapply source_table_safe_refine.
  - apply source_refinesb_spec. exact Href.
  - exact Hroster.
Qed.

Definition agent50_child_side_remaining : list TM :=
  filter
    (fun child => negb (agent50_source_roster_covers_tm
      agent50_child_side_roster child))
    chunk2_first_hole_children.

Theorem agent50_child_side_remaining_sound bound roster nodes :
  Forall (source_table_safe bound) roster ->
  Forall (source_table_safe bound)
    (filter (fun child => negb (agent50_source_roster_covers_tm roster child)) nodes) ->
  Forall (source_table_safe bound) nodes.
Proof.
  intros Hroster Hrest.
  rewrite Forall_forall in Hrest |- *.
  intros child Hchild.
  destruct (agent50_source_roster_covers_tm roster child) eqn:E.
  - eapply agent50_source_roster_covers_tm_sound; eassumption.
  - apply Hrest. apply filter_In. split; [exact Hchild|].
    unfold negb. now rewrite E.
Qed.

Theorem agent50_child_side_frontier_sound bound :
  Forall (source_table_safe bound) agent50_child_side_remaining ->
  Forall (source_table_safe bound) chunk2_first_hole_children.
Proof.
  intro Hremaining.
  eapply agent50_child_side_remaining_sound.
  - apply agent50_child_side_roster_safe.
  - exact Hremaining.
Qed.

Theorem agent50_child_side_initial_safe bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) agent50_child_side_remaining ->
  safeQ (source_weighted_safe bound) (q_i 2 32).
Proof.
  intros Hbound Hremaining.
  apply chunk2_first_hole_initial_safe; [exact Hbound|].
  apply agent50_child_side_frontier_sound. exact Hremaining.
Qed.

(* Reproducible finite output: number of children certified by this first
   budget-zero pass, and number retained as open source obligations. *)
Time Eval vm_compute in
  (length chunk2_first_hole_children, length agent50_child_side_strings,
   length agent50_child_side_certificates, length agent50_child_side_remaining).

Print Assumptions agent50_child_side_roster_safe.
Print Assumptions agent50_child_side_frontier_sound.
Print Assumptions agent50_child_side_initial_safe.
