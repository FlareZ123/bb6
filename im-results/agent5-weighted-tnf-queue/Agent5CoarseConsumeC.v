From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5CoarseTree Agent5CoarseC.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List NArith Bool.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Definition coarse_q0_C := decode_queue Agent8PackedChunk.chunk_data.
Definition coarse_remaining_C := roster_remaining coarse_roster_C (fst coarse_q0_C ++ snd coarse_q0_C).
Theorem coarse_consume_C bound : 1000006 <= bound ->
 (Forall (source_weighted_safe bound) (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
  Forall (source_weighted_safe bound) coarse_remaining_C).
Proof. intro HB. apply roster_checkpoint_consumption.
 - eapply coarse_roster_mono; [exact HB|exact coarse_roster_C_safe].
 - exact Agent8PackedChunk.chunk_data_exact.
Qed.
Definition coarse_counts_C := (length (fst coarse_q0_C), length (snd coarse_q0_C), length (filter (source_roster_covers coarse_roster_C) (fst coarse_q0_C)), length (filter (source_roster_covers coarse_roster_C) (snd coarse_q0_C))).
Theorem coarse_counts_C_exact : coarse_counts_C = (156,1,1,0).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions coarse_consume_C.
Print Assumptions coarse_counts_C_exact.
