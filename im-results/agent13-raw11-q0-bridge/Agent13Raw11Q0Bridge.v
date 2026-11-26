(* 
   Corrected q0 interface.
   The nine-parent roster covers exactly 9 of 156 active checkpoint entries
   and none of the held entries. It does NOT cover the full Raw11 frontier.
   This file therefore exports the exact Raw11 frontier identification and
   the conditional q0 checkpoint-reduction theorem, not a Raw11 Cover.
*)
From BusyCoq Require Import
  Individual62 Enumerate62
  Agent47Q0NineParentMembership Agent47Raw11RestrictedQ0
  Agent8WeightedSource SourceResidualRoster.
From Coq Require Import List Lia.
Import ListNotations TNF_Node.
Open Scope nat_scope.

Theorem raw11_q0_restriction_is_local_frontier :
  raw11_q0_restriction = raw11_local_q0.
Proof.
  exact raw11_q0_restriction_exact.
Qed.

Theorem raw11_q0_nine_parent_counts :
  (List.length (fst q0_nine_queue),
   List.length (snd q0_nine_queue),
   List.length (filter (source_roster_covers q0_nine_parent_roster)
     (fst q0_nine_queue)),
   List.length (filter (source_roster_covers q0_nine_parent_roster)
     (snd q0_nine_queue))) = (156, 1, 9, 0).
Proof.
  exact q0_nine_parent_counts_exact.
Qed.

Theorem raw11_q0_nine_remaining_length :
  List.length q0_nine_remaining = 148.
Proof.
  exact q0_nine_remaining_length.
Qed.

(* Once the nine parent Covers are supplied, the global q0 adaptive
   obligations reduce exactly to the 148-entry remainder. The remaining
   entries are still obligations; no Raw11 parent Cover follows here. *)
Theorem raw11_q0_nine_parent_consumption bound :
  Forall (source_table_safe bound) q0_nine_parent_roster ->
  (Forall (source_weighted_safe bound)
      (adaptive_obligations decider (AP_advance 1000000 AP_stop) (q_i 0 100)) <->
   Forall (source_weighted_safe bound) q0_nine_remaining).
Proof.
  exact q0_nine_consumption.
Qed.

Print Assumptions raw11_q0_restriction_is_local_frontier.
Print Assumptions raw11_q0_nine_parent_counts.
Print Assumptions raw11_q0_nine_parent_consumption.
