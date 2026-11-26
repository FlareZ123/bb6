From BusyCoq Require Import Individual62 Enumerate62
  Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource
  SourceResidualRoster Agent5RosterComplement.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List Bool NArith Lia Strings.String.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Open Scope string_scope.

(* These are the nine exact active checkpoint parents refined by the 94
   q0-open-automata leaves. They are not the 94 leaves themselves. *)
Definition q0_nine_parent_roster : list TM :=
  [ TM_from_str "1RB1RD_1RC0RE_0LA0RF_1LA1LD_---0LA_------";
    TM_from_str "1RB1RD_1RC0RE_0LA---_1LA1LD_---0RB_------";
    TM_from_str "1RB1RD_1RC0RE_0LA---_1LA1LD_---1LB_------";
    TM_from_str "1RB1RD_1RC0RE_0LA---_1LA1LD_---1RC_------";
    TM_from_str "1RB1RD_1RC0RE_0LA---_1LA1LD_---0LE_------";
    TM_from_str "1RB1RD_1RC0RE_0LA---_1LA1LD_---1LE_------";
    TM_from_str "1RB1RD_1RC0RE_0LA---_1LA1LD_---0LF_------";
    TM_from_str "1RB1RD_1RC0RE_0LA---_1LA1LD_---0RF_------";
    TM_from_str "1RB1RD_1RC0RE_0LA---_1LA1LD_---1RF_------" ].

Definition q0_nine_queue := decode_queue Agent8PackedChunk.chunk_data.
Definition q0_nine_remaining :=
  roster_remaining q0_nine_parent_roster
    (List.app (fst q0_nine_queue) (snd q0_nine_queue)).

Fixpoint q0_nine_covered_indices (i : nat) (xs : list T) : list nat :=
  match xs with
  | [] => []
  | x :: rest =>
      if source_roster_covers q0_nine_parent_roster x
      then i :: q0_nine_covered_indices (S i) rest
      else q0_nine_covered_indices (S i) rest
  end.

Theorem q0_nine_parent_counts_exact :
  (length (fst q0_nine_queue), length (snd q0_nine_queue),
   length (filter (source_roster_covers q0_nine_parent_roster) (fst q0_nine_queue)),
   length (filter (source_roster_covers q0_nine_parent_roster) (snd q0_nine_queue))) =
  (156, 1, 9, 0).
Proof. vm_compute. reflexivity. Qed.

Theorem q0_nine_parent_indices_exact :
  q0_nine_covered_indices 0 (fst q0_nine_queue) =
    [26; 33; 34; 39; 44; 46; 48; 49; 51].
Proof. vm_compute. reflexivity. Qed.

Theorem q0_nine_remaining_length :
  length q0_nine_remaining = 148.
Proof. vm_compute. reflexivity. Qed.

(* Conditional source-queue reduction: once the nine parent Covers are
   supplied at a common bound, the exact q0 checkpoint can discard them
   while preserving all other active and held obligations. *)
Theorem q0_nine_consumption (bound : nat) :
  Forall (source_table_safe bound) q0_nine_parent_roster ->
  (Forall (source_weighted_safe bound)
      (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
   Forall (source_weighted_safe bound) q0_nine_remaining).
Proof.
  intro Hsafe.
  unfold q0_nine_remaining, q0_nine_queue.
  eapply roster_checkpoint_consumption; eauto using Agent8PackedChunk.chunk_data_exact.
Qed.

Print Assumptions q0_nine_parent_counts_exact.
Print Assumptions q0_nine_parent_indices_exact.
Print Assumptions q0_nine_remaining_length.
Print Assumptions q0_nine_consumption.
