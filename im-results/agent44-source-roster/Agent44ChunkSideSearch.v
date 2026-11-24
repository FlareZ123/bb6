From BusyCoq Require Import Agent47SourceChunk2 Agent47SourceWitness
  Agent8WeightedSource Agent8AdaptiveSource Agent32SourceBackwards
  Agent8PackedChunk2_32_32 Agent32SourceEncoding Enumerate62 Individual62.
From Coq Require Import List Bool Lia Arith NArith Strings.String
  Logic.FunctionalExtensionality.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.
Open Scope nat_scope.

(* A bounded, source-native search over the exact 50 residual nodes left by
   Agent47SourceChunk2. The verifier is the original TranslatedCyclers checker,
   not a Lean-side simulation or a heuristic acceptance predicate. *)

Definition side_candidate := (dir * (nat * (nat * nat)))%type.

Definition side_candidates : list side_candidate :=
  flat_map (fun d =>
    flat_map (fun entry =>
      flat_map (fun period =>
        map (fun budget => (d,(entry,(period,budget)))) (seq 0 3))
        (seq 1 13))
      (seq 0 13))
    [L;R].

Definition side_candidate_check (p : TM) (c : side_candidate) : bool :=
  let '(d,(entry,(period,budget))) := c in
  source_side_check p d entry period budget.

Definition find_side_candidate (p : TM) : option side_candidate :=
  find (side_candidate_check p) side_candidates.

Lemma find_first_true {A : Type} (f : A -> bool) (xs : list A) (x : A) :
  find f xs = Some x -> f x = true.
Proof.
  induction xs as [|a xs IH]; cbn; intro H.
  - discriminate.
  - destruct (f a) eqn:Ha.
    + inversion H; subst. exact Ha.
    + eapply IH. exact H.
Qed.

Lemma find_side_candidate_sound p c :
  find_side_candidate p = Some c -> side_candidate_check p c = true.
Proof.
  unfold find_side_candidate.
  apply find_first_true.
Qed.

Definition candidate_witness (c : side_candidate) : source_witness :=
  let '(d,entry,period,budget) := c in SWside d entry period budget.

Lemma source_certificate_check_of_candidate bound p c :
  side_candidate_check p c = true ->
  certificate_check bound (TM_to_str p, candidate_witness c) = true.
Proof.
  destruct c as [d [entry [period budget]]].
  unfold side_candidate_check, candidate_witness, certificate_check,
    certificate_tm, source_witness_check, source_side_check.
  cbn.
  assert (Htm : TM_from_str (TM_to_str p) = p).
  { apply functional_extensionality. intro s.
    apply agent32_table_roundtrip. }
  rewrite Htm.
  exact H.
Qed.

Fixpoint search_side_roster (xs : list T) : list source_certificate :=
  match xs with
  | [] => []
  | x :: rest =>
      match find_side_candidate (tm x) with
      | Some c =>
          (TM_to_str (tm x), candidate_witness c) :: search_side_roster rest
      | None => search_side_roster rest
      end
  end.

Theorem search_side_roster_checked bound xs :
  forallb (certificate_check bound) (search_side_roster xs) = true.
Proof.
  induction xs as [|x xs IH]; cbn [search_side_roster].
  - reflexivity.
  - destruct (find_side_candidate (tm x)) as [c|] eqn:Hfind; cbn.
    + apply andb_true_intro. split.
      * apply source_certificate_check_of_candidate.
        apply find_side_candidate_sound. exact Hfind.
      * exact IH.
    + exact IH.
Qed.

Definition searched_chunk_certs : list source_certificate :=
  search_side_roster chunk_remaining.

Definition searched_chunk_roster : list TM :=
  certificate_roster searched_chunk_certs.

Definition searched_chunk_remaining : list T :=
  source_uncovered searched_chunk_roster chunk_remaining.

Theorem searched_chunk_roster_safe bound :
  Forall (source_table_safe bound) searched_chunk_roster.
Proof.
  unfold searched_chunk_roster, searched_chunk_certs.
  apply certificate_roster_safe.
  apply search_side_roster_checked.
Qed.

Theorem searched_chunk_actual_residuals_sound bound :
  Forall (source_weighted_safe bound) searched_chunk_remaining ->
  safeQ (source_weighted_safe bound)
    (SearchQueue_upds decider (q_i 2 32) 32%N).
Proof.
  intro H.
  rewrite packed_chunk_2_32_32_exact.
  unfold safeQ. split.
  - eapply source_uncovered_sound; [apply searched_chunk_roster_safe|exact H].
  - change (Forall (source_weighted_safe bound) []). constructor.
Qed.

Theorem chunk_initial_safe_of_search bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_weighted_safe bound) searched_chunk_remaining ->
  safeQ (source_weighted_safe bound) (q_i 2 32).
Proof.
  intros HB H.
  apply (source_updates_backwards (source_weighted_safe bound)
    decider (source_weighted_local bound HB) (q_i 2 32) 32%N).
  apply searched_chunk_actual_residuals_sound. exact H.
Qed.

(* The report is deliberately finite and reproducible: it records the number
   of new certificates and the exact number of remaining source obligations. *)
Time Eval vm_compute in
  (length searched_chunk_certs, length searched_chunk_remaining).
Time Eval vm_compute in (map fst searched_chunk_certs).

Print Assumptions searched_chunk_roster_safe.
Print Assumptions searched_chunk_actual_residuals_sound.
Print Assumptions chunk_initial_safe_of_search.
