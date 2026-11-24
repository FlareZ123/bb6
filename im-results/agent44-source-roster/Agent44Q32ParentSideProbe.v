From BusyCoq Require Import Enumerate62 Individual62 TranslatedCyclers
  Agent44Q32CanonicalParent.
From Coq Require Import List Bool Arith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* A source-only probe for one certificate on the common parent of the
   q_i(2,32) checkpoint. This intentionally avoids Agent8WeightedSource:
   the computation only asks the original TranslatedCyclers checker whether
   one bounded SWside witness exists for the canonical parent. *)
Module Agent47TC := TranslatedCyclers BB62.

Definition q32_parent_side_candidate := (dir * (nat * (nat * nat)))%type.

Definition q32_parent_side_candidates : list q32_parent_side_candidate :=
  flat_map (fun d =>
    flat_map (fun entry =>
      flat_map (fun period =>
        map (fun budget => (d,(entry,(period,budget)))) (seq 0 3))
        (seq 1 13))
      (seq 0 13))
    [L;R].

Definition q32_parent_side_candidate_check
    (p : TM) (c : q32_parent_side_candidate) : bool :=
  let '(d,(entry,(period,budget))) := c in
  if Agent47TC.verify_tcycler p d entry period budget then true else false.

Definition q32_find_parent_side_candidate : option q32_parent_side_candidate :=
  find (q32_parent_side_candidate_check
    (TM_from_str (TM_to_str q32_canonical_residual_7)))
    q32_parent_side_candidates.

Lemma q32_find_first_true {A : Type} (f : A -> bool) (xs : list A) (x : A) :
  find f xs = Some x -> f x = true.
Proof.
  induction xs as [|a xs IH]; cbn; intro H.
  - discriminate.
  - destruct (f a) eqn:Ha.
    + inversion H; subst. exact Ha.
    + eapply IH. exact H.
Qed.

Theorem q32_parent_side_candidate_sound c :
  q32_find_parent_side_candidate = Some c ->
  q32_parent_side_candidate_check
    (TM_from_str (TM_to_str q32_canonical_residual_7)) c = true.
Proof.
  unfold q32_find_parent_side_candidate.
  apply q32_find_first_true.
Qed.

Time Eval vm_compute in List.length q32_parent_side_candidates.
Time Eval vm_compute in q32_find_parent_side_candidate.
Print Assumptions q32_parent_side_candidate_sound.
