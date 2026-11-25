From BusyCoq Require Import Agent47SourceWitness Agent8WeightedSource TC62
  Enumerate62 Individual62.
From Coq Require Import List Bool Lia Arith NArith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.
Open Scope nat_scope.

(* Three distinct image cylinders left outside the 121-table roster and all
   37 already-available source witnesses by the finite S4 cover audit. *)
Definition s4_gap129_tm : TM :=
  TM_from_str "1RB---_1RC---_0RD---_1LD1RE_------_------".

Definition s4_gap142_tm : TM :=
  TM_from_str "1RB---_1RC---_0RD---_------_------_------".

Definition s4_gap152_tm : TM :=
  TM_from_str "1RB---_1RC---_------_------_------_------".

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
  let '(d,(entry,(period,budget))) := c in SWside d entry period budget.

Lemma source_certificate_check_of_candidate bound p c :
  side_candidate_check (TM_from_str (TM_to_str p)) c = true ->
  certificate_check bound (TM_to_str p, candidate_witness c) = true.
Proof.
  destruct c as [d [entry [period budget]]].
  change (source_side_check (TM_from_str (TM_to_str p))
    d entry period budget = true) in H.
  unfold candidate_witness, certificate_check, certificate_tm,
    source_witness_check.
  cbn.
  exact H.
Qed.

Definition gap_certificate (p : TM) : list source_certificate :=
  match find_side_candidate (TM_from_str (TM_to_str p)) with
  | Some c => [(TM_to_str p, candidate_witness c)]
  | None => []
  end.

Definition s4_gap_certificates : list source_certificate :=
  gap_certificate s4_gap129_tm ++
  gap_certificate s4_gap142_tm ++
  gap_certificate s4_gap152_tm.

Lemma gap_certificate_checked bound p :
  forallb (certificate_check bound) (gap_certificate p) = true.
Proof.
  unfold gap_certificate.
  destruct (find_side_candidate (TM_from_str (TM_to_str p))) as [c|] eqn:Hfind; cbn.
  - apply source_certificate_check_of_candidate.
    apply find_side_candidate_sound. exact Hfind.
  - reflexivity.
Qed.

Theorem s4_gap_certificates_checked bound :
  forallb (certificate_check bound) s4_gap_certificates = true.
Proof.
  unfold s4_gap_certificates.
  rewrite !forallb_app.
  repeat rewrite gap_certificate_checked.
  reflexivity.
Qed.

Theorem s4_gap_roster_safe bound :
  Forall (source_table_safe bound) (certificate_roster s4_gap_certificates).
Proof.
  apply certificate_roster_safe.
  apply s4_gap_certificates_checked.
Qed.

Time Eval vm_compute in
  (find_side_candidate (TM_from_str (TM_to_str s4_gap129_tm)),
   find_side_candidate (TM_from_str (TM_to_str s4_gap142_tm)),
   find_side_candidate (TM_from_str (TM_to_str s4_gap152_tm))).

Time Eval vm_compute in
  (length s4_gap_certificates, map fst s4_gap_certificates).

Print Assumptions s4_gap_roster_safe.
