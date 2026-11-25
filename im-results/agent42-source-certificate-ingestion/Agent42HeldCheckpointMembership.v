From BusyCoq Require Import Enumerate62 Agent8AdaptiveSource
  SourceResidualRoster Agent5RecoveredHeld.
From Coq Require Import List NArith Strings.String Classical_Prop.
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

Lemma recovered_held_2800_refines_parent :
    source_refinesb recovered_held_2800 recovered_held_2800_parent = true.
Proof.
  vm_compute.
Qed.

Lemma recovered_held_2800_child_of_parent :
    is_child_of recovered_held_2800 recovered_held_2800_parent.
Proof.
  exact ((source_refinesb_spec recovered_held_2800
    recovered_held_2800_parent).mp recovered_held_2800_refines_parent).
Qed.

/-- Source-side complement preservation: every completion of the parent
    either extends the FARv3-certified leaf, or disagrees with it at a slot
    left open by the parent and fixed by the leaf. -/
Theorem recovered_held_2800_parent_leaf_partition (m : TM)
    (hm : is_child_of m recovered_held_2800_parent) :
    is_child_of m recovered_held_2800 \\/
      exists h,
        recovered_held_2800_parent h = None /\\
        recovered_held_2800 h <> None /\\
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

(* Test the actual held checkpoint, not a copied table string or a count:
    some held node is a source refinement of the independently certified
    FARv3 residual. *)
Definition recovered_held_2800_checkpoint_memberb : bool :=
  existsb
    (fun x => source_refinesb (tm x) recovered_held_2800)
    (snd recovered_held_2800_checkpoint).

Theorem recovered_held_2800_checkpoint_member :
    recovered_held_2800_checkpoint_memberb = true.
Proof.
  vm_compute.
Qed.

Theorem recovered_held_2800_checkpoint_leaf :
    exists x,
      In x (snd recovered_held_2800_checkpoint) /\
      is_child_of (tm x) recovered_held_2800.
Proof.
  pose proof recovered_held_2800_checkpoint_member as H.
  unfold recovered_held_2800_checkpoint_memberb,
    recovered_held_2800_checkpoint in H.
  apply existsb_exists in H.
  destruct H as [x [Hx Href]].
  exists x.
  split.
  - exact Hx.
  - apply source_refinesb_spec.
    exact Href.
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
  destruct recovered_held_2800_checkpoint_leaf as [x [Hx Href]].
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
