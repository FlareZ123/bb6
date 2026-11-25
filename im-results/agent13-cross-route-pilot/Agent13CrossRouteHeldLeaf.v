From BusyCoq Require Import CTL62 SourceResidualRoster Agent5RecoveredHeld.
From Coq Require Import Strings.String.
Open Scope string_scope.

(* The root residual at address B0=1LC in RootFrontier.root-frontier.json. *)
Definition first_one_root : TM :=
  TM_from_str "1RB---_------_------_------_------_------".

Definition first_one_B0_1LC : TM :=
  TM_from_str "1RB---_1LC---_------_------_------_------".

Lemma first_one_B0_1LC_refines_root :
  source_refinesb first_one_B0_1LC first_one_root = true.
Proof. vm_compute. Qed.

Lemma recovered_held_2800_refines_B0_1LC :
  source_refinesb recovered_held_2800 first_one_B0_1LC = true.
Proof. vm_compute. Qed.

Theorem recovered_held_2800_child_of_first_one_root :
  is_child_of recovered_held_2800 first_one_root.
Proof.
  apply source_refinesb_spec.
  eapply child_trans.
  - apply source_refinesb_spec.
    exact recovered_held_2800_refines_B0_1LC.
  - apply source_refinesb_spec.
    exact first_one_B0_1LC_refines_root.
Qed.

Theorem recovered_held_2800_safe_for_all_bounds :
  forall bound, source_table_safe bound recovered_held_2800.
Proof.
  intro bound.
  exact (recovered_held_2800_safe bound).
Qed.

Print Assumptions recovered_held_2800_child_of_first_one_root.
Print Assumptions recovered_held_2800_safe_for_all_bounds.
