From BusyCoq Require Import Agent47SourceChunk2 Agent47SourceTree
  Enumerate62 Individual62 Agent8WeightedSource.
From Coq Require Import List Bool Lia Arith NArith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* The 50 source-table residuals left by the exact q_i(2,32), fuel-32
   checkpoint all reach an undefined row within 18 ordinary moves. This file
   turns that finite trace fact into a source-tree split. Each split retains
   all 24 ordinary transition completions; only the first-hole halt branch is
   discharged by source_first_hole_split. *)

Definition chunk2_hole_slots : list (Q * Sym) :=
  flat_map (fun q => map (fun s => (q,s)) all_syms) all_qs.

Definition chunk2_hole_candidates : list (nat * (Q * Sym)) :=
  flat_map (fun n => map (fun h => (n,h)) chunk2_hole_slots) (seq 0 19).

Definition find_chunk2_hole (p : TM) : option (nat * (Q * Sym)) :=
  find (fun nh => source_hole_atb p (fst nh) (snd nh))
    chunk2_hole_candidates.

Lemma find_first_true {A : Type} (f : A -> bool) (xs : list A) (x : A) :
  find f xs = Some x -> f x = true.
Proof.
  induction xs as [|a xs IH]; cbn; intro H.
  - discriminate.
  - destruct (f a) eqn:Ha.
    + inversion H; subst. exact Ha.
    + eapply IH. exact H.
Qed.

Lemma find_chunk2_hole_sound p n h :
  find_chunk2_hole p = Some (n,h) ->
  source_hole_atb p n h = true.
Proof.
  unfold find_chunk2_hole. intro H.
  pose proof (find_first_true _ _ _ H) as Htrue.
  cbn in Htrue. exact Htrue.
Qed.

Definition chunk2_first_hole_tree (p : TM) : source_tree :=
  match find_chunk2_hole p with
  | Some (n,h) => STsplit n h (fun _ => STopen)
  | None => STopen
  end.

Lemma chunk2_first_hole_tree_check_of_find bound p n h :
  find_chunk2_hole p = Some (n,h) ->
  n + 6 <= bound ->
  source_tree_check bound p (chunk2_first_hole_tree p) = true.
Proof.
  intros Hfind Hbound.
  unfold chunk2_first_hole_tree. rewrite Hfind.
  cbn [source_tree_check].
  apply andb_true_iff. split.
  - apply Nat.leb_le. exact Hbound.
  - apply andb_true_iff. split.
    + apply find_chunk2_hole_sound. exact Hfind.
    + apply forallb_forall. intros v Hv. reflexivity.
Qed.

Definition chunk2_first_hole_within18 (x : T) : bool :=
  match find_chunk2_hole (tm x) with
  | Some (n,_) => Nat.leb n 18
  | None => false
  end.

Theorem chunk2_first_hole_search_complete :
  forallb chunk2_first_hole_within18 chunk_remaining = true.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma chunk2_first_hole_bound x :
  In x chunk_remaining ->
  exists n h, find_chunk2_hole (tm x) = Some (n,h) /\ n + 6 <= 24.
Proof.
  intro Hx.
  pose proof
    (proj1 (forallb_forall chunk2_first_hole_within18 chunk_remaining)
      chunk2_first_hole_search_complete x Hx) as H.
  unfold chunk2_first_hole_within18 in H.
  destruct (find_chunk2_hole (tm x)) as [[n h]|] eqn:E; [|discriminate].
  apply Nat.leb_le in H.
  exists n,h. split; [exact E|lia].
Qed.

Theorem chunk2_first_hole_tree_checks bound :
  24 <= bound ->
  forallb
    (fun x => source_tree_check bound (tm x) (chunk2_first_hole_tree (tm x)))
    chunk_remaining = true.
Proof.
  intros Hbound.
  apply forallb_forall. intros x Hx.
  destruct (chunk2_first_hole_bound x Hx) as [n [h [Hfind Hn]]].
  eapply chunk2_first_hole_tree_check_of_find; [exact Hfind|lia].
Qed.

Definition chunk2_first_hole_children : list TM :=
  flat_map
    (fun x => source_tree_open (tm x) (chunk2_first_hole_tree (tm x)))
    chunk_remaining.

Theorem chunk2_first_hole_children_count :
  length chunk2_first_hole_children = 1200%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Theorem chunk2_first_hole_frontier_sound bound :
  24 <= bound ->
  Forall (source_table_safe bound) chunk2_first_hole_children ->
  Forall (source_table_safe bound) chunk_remaining.
Proof.
  intros Hbound Hchildren.
  apply Forall_forall. intros x Hx.
  assert (Hcheck :
    source_tree_check bound (tm x) (chunk2_first_hole_tree (tm x)) = true).
  { exact
      (proj1
        (forallb_forall
          (fun y => source_tree_check bound (tm y) (chunk2_first_hole_tree (tm y)))
          chunk_remaining)
        (chunk2_first_hole_tree_checks bound Hbound) x Hx). }
  assert (Hopen :
    Forall (source_table_safe bound)
      (source_tree_open (tm x) (chunk2_first_hole_tree (tm x)))).
  { apply Forall_forall. intros m Hm.
    pose proof (proj1 (Forall_forall (source_table_safe bound)
      chunk2_first_hole_children) Hchildren m) as Hall.
    apply Hall.
    unfold chunk2_first_hole_children.
    apply in_flat_map. exists x. split; assumption. }
  exact (source_tree_sound bound (tm x) (chunk2_first_hole_tree (tm x))
    Hcheck Hopen).
Qed.

Lemma chunk2_source_table_safe_to_weighted bound x :
  source_table_safe bound (tm x) -> source_weighted_safe bound x.
Proof.
  intros Hsafe _ t Hchild. exact (Hsafe t Hchild).
Qed.

Theorem chunk2_first_hole_initial_safe bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) chunk2_first_hole_children ->
  safeQ (source_weighted_safe bound) (q_i 2 32).
Proof.
  intros Hbound Hchildren.
  apply chunk_initial_safe_of_remaining.
  - exact Hbound.
  - apply Forall_forall. intros x Hx.
    apply chunk2_source_table_safe_to_weighted.
    pose proof (chunk2_first_hole_frontier_sound bound ltac:(lia) Hchildren) as Hsafe.
    exact (proj1 (Forall_forall (source_table_safe bound) chunk_remaining)
      Hsafe x Hx).
Qed.

Print Assumptions chunk2_first_hole_search_complete.
Print Assumptions chunk2_first_hole_frontier_sound.
Print Assumptions chunk2_first_hole_initial_safe.
