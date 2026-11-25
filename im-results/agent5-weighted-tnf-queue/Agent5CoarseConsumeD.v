From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5CoarseTree Agent5CoarseD.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List NArith Bool.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Definition coarse_q0_D := decode_queue Agent8PackedChunk.chunk_data.
Definition coarse_remaining_D := roster_remaining coarse_roster_D (fst coarse_q0_D ++ snd coarse_q0_D).
Theorem coarse_consume_D bound : 1000006 <= bound ->
 (Forall (source_weighted_safe bound) (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
  Forall (source_weighted_safe bound) coarse_remaining_D).
Proof. intro HB. apply roster_checkpoint_consumption.
 - eapply coarse_roster_mono; [exact HB|exact coarse_roster_D_safe].
 - exact Agent8PackedChunk.chunk_data_exact.
Qed.
Definition coarse_counts_D := (length (fst coarse_q0_D), length (snd coarse_q0_D), length (filter (source_roster_covers coarse_roster_D) (fst coarse_q0_D)), length (filter (source_roster_covers coarse_roster_D) (snd coarse_q0_D))).
Theorem coarse_counts_D_exact : coarse_counts_D = (156,1,1,0).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions coarse_consume_D.
Print Assumptions coarse_counts_D_exact.
