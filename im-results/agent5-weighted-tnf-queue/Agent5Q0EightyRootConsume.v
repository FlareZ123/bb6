From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5CoarseTree Agent5CoarseConsumeAll Agent5Q0FiveRootConsume.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List NArith Bool.
Import ListNotations TNF_Node.
Open Scope nat_scope.

Definition q0_80_roster : list TM := coarse_roster_All ++ q0_five_roster.
Theorem q0_80_roster_safe :
  Forall (source_table_safe 1000006) q0_80_roster.
Proof.
  unfold q0_80_roster. apply Forall_app.
  split; [exact coarse_roster_All_safe|exact q0_five_roster_safe].
Qed.

Definition q0_80_queue := decode_queue Agent8PackedChunk.chunk_data.
Definition q0_80_remaining :=
  roster_remaining q0_80_roster (fst q0_80_queue ++ snd q0_80_queue).

Theorem q0_80_consume bound : 1000006 <= bound ->
  (Forall (source_weighted_safe bound)
    (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
   Forall (source_weighted_safe bound) q0_80_remaining).
Proof.
  intro HB. apply roster_checkpoint_consumption.
  - eapply coarse_roster_mono with (lo:=1000006); [exact HB|].
    exact q0_80_roster_safe.
  - exact Agent8PackedChunk.chunk_data_exact.
Qed.

Theorem q0_80_counts_exact :
  (length (fst q0_80_queue), length (snd q0_80_queue),
   length (filter (source_roster_covers q0_80_roster) (fst q0_80_queue)),
   length (filter (source_roster_covers q0_80_roster) (snd q0_80_queue))) = (156,1,80,0).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions q0_80_roster_safe.
Print Assumptions q0_80_consume.
Print Assumptions q0_80_counts_exact.
