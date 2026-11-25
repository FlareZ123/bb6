From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5CoarseTree Agent5CoarseSmall Agent5CoarseA Agent5CoarseB Agent5CoarseC Agent5CoarseD.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List NArith Bool.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Definition coarse_roster_All := coarse_roster_Small ++ coarse_roster_A ++ coarse_roster_B ++ coarse_roster_C ++ coarse_roster_D.
Theorem coarse_roster_All_safe : Forall (source_table_safe 1000006) coarse_roster_All.
Proof. unfold coarse_roster_All. apply Forall_app. split; [exact coarse_roster_Small_safe|]. apply Forall_app. split; [exact coarse_roster_A_safe|]. apply Forall_app. split; [exact coarse_roster_B_safe|]. apply Forall_app. split; [exact coarse_roster_C_safe|]. exact coarse_roster_D_safe. Qed.
Definition coarse_q0_All := decode_queue Agent8PackedChunk.chunk_data.
Definition coarse_remaining_All := roster_remaining coarse_roster_All (fst coarse_q0_All ++ snd coarse_q0_All).
Theorem coarse_consume_All bound : 1000006 <= bound ->
 (Forall (source_weighted_safe bound) (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
  Forall (source_weighted_safe bound) coarse_remaining_All).
Proof. intro HB. apply roster_checkpoint_consumption.
 - eapply coarse_roster_mono; [exact HB|exact coarse_roster_All_safe].
 - exact Agent8PackedChunk.chunk_data_exact.
Qed.
Definition coarse_counts_All := (length (fst coarse_q0_All), length (snd coarse_q0_All), length (filter (source_roster_covers coarse_roster_All) (fst coarse_q0_All)), length (filter (source_roster_covers coarse_roster_All) (snd coarse_q0_All))).
Theorem coarse_counts_All_exact : coarse_counts_All = (156,1,75,0).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions coarse_consume_All.
Print Assumptions coarse_counts_All_exact.
