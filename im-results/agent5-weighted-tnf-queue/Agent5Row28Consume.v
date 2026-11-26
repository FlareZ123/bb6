From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5CoarseTree Agent5Row28Data.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List NArith Bool Lia.
Import ListNotations TNF_Node.
Open Scope nat_scope.

Definition row28_roster : list TM := [row28_parent].
Lemma row28_roster_safe bound : 63 <= bound -> Forall (source_table_safe bound) row28_roster.
Proof.
  intro Hb. eapply coarse_roster_mono with (lo:=63); [exact Hb|].
  unfold row28_roster. constructor; [exact row28_safe|constructor].
Qed.
Definition row28_q0 := decode_queue Agent8PackedChunk.chunk_data.
Definition row28_remaining := roster_remaining row28_roster (fst row28_q0 ++ snd row28_q0).
Theorem row28_consume bound : 1000006 <= bound ->
  (Forall (source_weighted_safe bound) (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
   Forall (source_weighted_safe bound) row28_remaining).
Proof.
  intro HB. apply roster_checkpoint_consumption.
  - apply row28_roster_safe. lia.
  - exact Agent8PackedChunk.chunk_data_exact.
Qed.
Theorem row28_counts_exact :
  (length (fst row28_q0), length (snd row28_q0),
   length (filter (source_roster_covers row28_roster) (fst row28_q0)),
   length (filter (source_roster_covers row28_roster) (snd row28_q0))) = (156,1,1,0).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions row28_consume.
Print Assumptions row28_counts_exact.
