From BusyCoq Require Import Agent47SourceWitness Agent47SourceSweep
  Agent8PackedChunk2_32_32 Agent8QueueCheckpoint Agent8AdaptiveSource
  Agent32SourceBackwards SourceResidualRoster Agent8WeightedSource
  Enumerate62 Individual62.
From Coq Require Import List Bool NArith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.

Definition chunk_side_certs : list source_certificate := [
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------", SWside L 7 6 0);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RA_------", SWside L 7 7 0);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LB_------", SWside L 8 10 0);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RB_------", SWside R 12 10 0);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LB_------", SWside L 9 3 1);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LC_------", SWside L 0 13 2);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RC_------", SWside L 8 9 0);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LD_------", SWside L 7 7 0);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RD_------", SWside L 7 7 0);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LD_------", SWside L 7 7 0);
  ("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RD_------", SWside L 8 7 0);
  ("1RB1RD_1RC1RB_0LA---_1LA0LB_------_------", SWside R 1 7 0);
  ("1RB1RD_1RC0RC_0LA---_1LA0LB_------_------", SWside R 0 9 0);
  ("1RB1RD_1RC1RC_0LA---_1LA0LB_------_------", SWside R 2 6 1);
  ("1RB1RD_1RC0LD_0LA---_1LA0LB_------_------", SWside L 7 11 0);
  ("1RB1RD_1RC0RD_0LA---_1LA0LB_------_------", SWside R 7 3 0);
  ("1RB1RD_1RC1LD_0LA---_1LA0LB_------_------", SWside L 7 11 0);
  ("1RB1RD_1RC1RD_0LA---_1LA0LB_------_------", SWside R 4 4 1);
  ("1RB1RD_1RC---_0LA---_1LA0RB_------_------", SWside R 1 6 0);
  ("1RB1RD_1RC---_0LA---_1LA1RB_------_------", SWside R 1 6 0);
  ("1RB1RD_1RC---_0LA---_1LA0RC_------_------", SWside R 0 8 0);
  ("1RB1RD_1RC---_0LA---_1LA1RC_------_------", SWside R 2 5 1);
  ("1RB1RD_1RC---_0LA---_1LA1RD_------_------", SWside R 4 3 1);
  ("1RB1RD_1RC---_0LA---_1RA---_------_------", SWside R 0 5 0);
  ("1RB1RD_1RC---_0LA---_0RB---_------_------", SWside R 1 4 0);
  ("1RB1RD_1RC---_0LA---_1RB---_------_------", SWside R 1 4 0);
  ("1RB1RD_1RC---_0LA---_0RC---_------_------", SWside R 0 6 0);
  ("1RB1RD_1RC---_0LA---_1RC---_------_------", SWside R 2 3 1);
  ("1RB1RD_1RC---_0LA---_0RD---_------_------", SWside R 4 1 0);
  ("1RB1RD_1RC---_0LA---_1RD---_------_------", SWside R 4 1 0);
  ("1RB1LD_1RC---_0LA---_---1RA_------_------", SWside R 3 2 1);
  ("1RB1LD_1RC---_0LA---_---0LC_------_------", SWside L 0 6 2)
].

Theorem chunk_side_checked bound :
  forallb (certificate_check bound) chunk_side_certs = true.
Proof. vm_compute. reflexivity. Qed.

Definition chunk_roster : list TM :=
  certificate_roster chunk_side_certs ++ [sweep_tm true; sweep_tm false].

Theorem chunk_roster_safe bound :
  Forall (source_table_safe bound) chunk_roster.
Proof.
  unfold chunk_roster. apply Forall_app. split.
  - apply certificate_roster_safe. apply chunk_side_checked.
  - constructor.
    + apply source_nonhalt_cylinder. apply sweep_nonhalt.
    + constructor.
      * apply source_nonhalt_cylinder. apply sweep_nonhalt.
      * constructor.
Qed.

Definition chunk_remaining :=
  source_uncovered chunk_roster (fst (decode_queue packed_chunk_2_32_32)).

Theorem chunk_remaining_count : List.length chunk_remaining = 50%nat.
Proof. vm_compute. reflexivity. Qed.

(* The exact source checkpoint equation transports the reduced obligation
   list back to its original queue; no digest or cardinality is used. *)
Theorem chunk_actual_residuals_sound bound :
  Forall (source_weighted_safe bound) chunk_remaining ->
  safeQ (source_weighted_safe bound)
    (SearchQueue_upds decider (q_i 2 32) 32%N).
Proof.
  intro H. rewrite packed_chunk_2_32_32_exact.
  unfold safeQ. split.
  - eapply source_uncovered_sound; [apply chunk_roster_safe|exact H].
  - change (Forall (source_weighted_safe bound) []). constructor.
Qed.

Theorem chunk_initial_safe_of_remaining bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_weighted_safe bound) chunk_remaining ->
  safeQ (source_weighted_safe bound) (q_i 2 32).
Proof.
  intros HB H.
  apply (source_updates_backwards (source_weighted_safe bound)
    decider (source_weighted_local bound HB) (q_i 2 32) 32%N).
  apply chunk_actual_residuals_sound. exact H.
Qed.

Print Assumptions chunk_roster_safe.
Print Assumptions chunk_actual_residuals_sound.
Print Assumptions chunk_initial_safe_of_remaining.
