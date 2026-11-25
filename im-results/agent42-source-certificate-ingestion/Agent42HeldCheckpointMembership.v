From BusyCoq Require Import Enumerate62 CTL62 Individual62 Agent8AdaptiveSource
  Agent8WeightedSource SourceResidualRoster Agent5RecoveredHeld.
From Coq Require Import List Bool NArith Strings.String Classical_Prop.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.
Open Scope string_scope.

(* The exact source update checkpoint used by the recovered FARv3 leaf.
    The adaptive plan below stops here, so both active and held nodes remain
    obligations. *)

(* The exact depth-one source parent at address B0=1LC. *)
Definition recovered_held_2800_parent : TM :=
  TM_from_str "1RB---_1LC---_------_------_------_------".

Lemma recovered_held_2800_child_of_parent :
    is_child_of recovered_held_2800 recovered_held_2800_parent.
Proof.
  unfold is_child_of.
  intros [q s].
  destruct q; destruct s; vm_compute;
    try (left; reflexivity);
    right; reflexivity.
Qed.

Lemma recovered_held_2800_refines_parent :
    source_refinesb recovered_held_2800 recovered_held_2800_parent = true.
Proof.
  apply (proj2 (source_refinesb_spec _ _)).
  exact recovered_held_2800_child_of_parent.
Qed.

(* Source-side complement preservation: every completion of the parent
    either extends the FARv3-certified leaf, or disagrees with it at a slot
    left open by the parent and fixed by the leaf. *)
Theorem recovered_held_2800_parent_leaf_partition (m : TM)
    (hm : is_child_of m recovered_held_2800_parent) :
    is_child_of m recovered_held_2800 \/
      exists h,
        recovered_held_2800_parent h = None /\
        recovered_held_2800 h <> None /\
        m h <> recovered_held_2800 h.
Proof.
  destruct (classic (is_child_of m recovered_held_2800)) as [Hleaf|Hnot].
  - left. exact Hleaf.
  - right.
    unfold is_child_of in Hnot.
    apply not_all_ex_not in Hnot.
    destruct Hnot as [h Hbad].
    assert (HleafAssigned : recovered_held_2800 h <> None).
    { intro E. apply Hbad. left. exact E. }
    assert (Hmismatch : m h <> recovered_held_2800 h).
    { intro E. apply Hbad. right. exact E. }
    assert (HparentNone : recovered_held_2800_parent h = None).
    { destruct (recovered_held_2800_parent h) as [v|] eqn:Ep.
      2: reflexivity.
      pose proof (hm h) as Hm.
      pose proof (recovered_held_2800_child_of_parent h) as Hc.
      destruct Hm as [Hnone|Hsame]; [congruence|].
      destruct Hc as [Hnone|HsameLeaf]; [congruence|].
      apply Hmismatch.
      rewrite HsameLeaf.
      exact Hsame.
    }
    exists h.
    repeat split; assumption.
Qed.

Definition recovered_held_2800_checkpoint :=
  SearchQueue_upds decider (q_i 2800 100) 1000000%N.

(* Exact pointwise table equality, computed from the source transition
    serializer. This avoids relying on the source roster's boolean checker
    to perform the search; its correctness is proved below. *)
Definition source_table_eqb (a b : TM) : bool :=
  forallb (fun q => forallb (fun s =>
    String.eqb (Trans_to_str (a (q,s))) (Trans_to_str (b (q,s))))
    all_syms) all_qs.

Lemma Trans_to_str_injective (x y : option (Sym * dir * Q)) :
    Trans_to_str x = Trans_to_str y -> x = y.
Proof.
  destruct x as [[w [d q]]|]; destruct y as [[w' [d' q']]|];
    simpl; try discriminate.
  intro H.
  destruct w, w', d, d', q, q'; simpl in H; try discriminate; reflexivity.
Qed.

Theorem source_table_eqb_spec (a b : TM) :
    source_table_eqb a b = true ->
    is_child_of a b /\ is_child_of b a.
Proof.
  unfold source_table_eqb.
  intro H.
  assert (Hstr : forall q s,
      Trans_to_str (a (q,s)) = Trans_to_str (b (q,s))).
  { intros q s.
    assert (Hq : In q all_qs) by apply all_qs_spec.
    assert (Hs : In s all_syms) by apply all_syms_spec.
    apply forallb_forall with (x:=q) in H; [|exact Hq].
    apply forallb_forall with (x:=s) in H; [|exact Hs].
    apply String.eqb_eq in H.
    exact H.
  }
  split; intros [q s]; right.
  - apply Trans_to_str_injective.
    exact (Hstr q s).
  - apply Trans_to_str_injective.
    symmetry.
    exact (Hstr q s).
Qed.

(* Test the actual held checkpoint using exact source-table equality, not a
    copied JSON string or a count. *)
Definition recovered_held_2800_checkpoint_memberb : bool :=
  existsb
    (fun x => source_table_eqb (tm x) recovered_held_2800)
    (snd recovered_held_2800_checkpoint).

Theorem recovered_held_2800_checkpoint_member :
    recovered_held_2800_checkpoint_memberb = true.
Proof.
  vm_compute.
Qed.

Theorem recovered_held_2800_checkpoint_leaf :
    exists x,
      In x (snd recovered_held_2800_checkpoint) /\
      is_child_of (tm x) recovered_held_2800 /\
      is_child_of recovered_held_2800 (tm x).
Proof.
  pose proof recovered_held_2800_checkpoint_member as H.
  unfold recovered_held_2800_checkpoint_memberb,
    recovered_held_2800_checkpoint in H.
  apply existsb_exists in H.
  destruct H as [x [Hx Href]].
  apply source_table_eqb_spec in Href.
  destruct Href as [Hforward Hbackward].
  exists x.
  repeat split; assumption.
Qed.

(* The source-roster consumer converts the FARv3 cylinder theorem into the
    exact weighted-safety predicate expected by Agent 5's adaptive queue
    coverage interface. The implication is for every completion of the
    checkpoint node, not only the displayed source table. *)
Theorem recovered_held_2800_checkpoint_leaf_safe
    (bound : nat) (x : T)
    (h : is_child_of (tm x) recovered_held_2800) :
    source_weighted_safe bound x.
Proof.
  apply source_roster_safe with (roster := [recovered_held_2800]).
  - constructor.
    + exact (recovered_held_2800_safe bound).
    + constructor.
  - unfold source_roster_covers.
    change source_refinesb (tm x) recovered_held_2800 = true.
    exact ((source_refinesb_spec (tm x) recovered_held_2800).mpr h).
Qed.

(* One exact held node of the finite q_i(2800,100) checkpoint is now
    discharged in the same adaptive-obligation language consumed by
    actual_source_chunks_packed_global_upper. Every other active/held node
    remains in the list and is not claimed safe by this pilot. *)
Theorem recovered_held_2800_adaptive_obligation
    (bound : nat) :
    exists x,
      In x
        (adaptive_obligations decider
          (AP_advance 1000000%N AP_stop)
          (q_i 2800 100)) /\
      source_weighted_safe bound x.
Proof.
  destruct recovered_held_2800_checkpoint_leaf as [x [Hx [Href Hback]]].
  exists x.
  constructor.
  - unfold adaptive_obligations.
    change In x (fst recovered_held_2800_checkpoint ++
      snd recovered_held_2800_checkpoint).
    apply in_or_app.
    right.
    exact Hx.
  - exact (recovered_held_2800_checkpoint_leaf_safe bound x Href).
Qed.

Theorem recovered_held_2800_adaptive_singleton_consumed
    (bound : nat) (x : T)
    (h : is_child_of (tm x) recovered_held_2800) :
    Forall (source_weighted_safe bound) [x].
Proof.
  constructor.
  - exact (recovered_held_2800_checkpoint_leaf_safe bound x h).
  - constructor.
Qed.

Print Assumptions recovered_held_2800_refines_parent.
Print Assumptions recovered_held_2800_parent_leaf_partition.
Print Assumptions recovered_held_2800_checkpoint_member.
Print Assumptions recovered_held_2800_checkpoint_leaf.
Print Assumptions recovered_held_2800_checkpoint_leaf_safe.
Print Assumptions recovered_held_2800_adaptive_obligation.
