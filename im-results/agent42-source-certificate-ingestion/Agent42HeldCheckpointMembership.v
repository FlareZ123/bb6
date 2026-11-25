From BusyCoq Require Import Enumerate62 Agent8AdaptiveSource
  SourceResidualRoster Agent5RecoveredHeld.
From Coq Require Import List NArith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* The exact source update checkpoint used by the recovered FARv3 leaf.
    The adaptive plan below stops here, so both active and held nodes remain
    obligations. *)
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
    simpl.
    apply source_refinesb_spec.
    exact h.
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
    cbn.
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

Print Assumptions recovered_held_2800_checkpoint_member.
Print Assumptions recovered_held_2800_checkpoint_leaf.
Print Assumptions recovered_held_2800_checkpoint_leaf_safe.
Print Assumptions recovered_held_2800_adaptive_obligation.
