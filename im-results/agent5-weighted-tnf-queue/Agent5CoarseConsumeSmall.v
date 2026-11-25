From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5CoarseTree Agent5CoarseSmall.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List NArith Bool.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Definition coarse_q0_Small := decode_queue Agent8PackedChunk.chunk_data.
Definition coarse_remaining_Small := roster_remaining coarse_roster_Small (fst coarse_q0_Small ++ snd coarse_q0_Small).
Theorem coarse_consume_Small bound : 1000006 <= bound ->
 (Forall (source_weighted_safe bound) (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
  Forall (source_weighted_safe bound) coarse_remaining_Small).
Proof. intro HB. apply roster_checkpoint_consumption.
 - eapply coarse_roster_mono; [exact HB|exact coarse_roster_Small_safe].
 - exact Agent8PackedChunk.chunk_data_exact.
Qed.
Definition coarse_counts_Small := (length (fst coarse_q0_Small), length (snd coarse_q0_Small), length (filter (source_roster_covers coarse_roster_Small) (fst coarse_q0_Small)), length (filter (source_roster_covers coarse_roster_Small) (snd coarse_q0_Small))).
Theorem coarse_counts_Small_exact : coarse_counts_Small = (156,1,70,0).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions coarse_consume_Small.
Print Assumptions coarse_counts_Small_exact.
