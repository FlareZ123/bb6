From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5CoarseTree Agent5Row26Data.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List NArith Bool Lia.
Import ListNotations TNF_Node.
Open Scope nat_scope.

Definition row26_roster : list TM := [row26_parent].
Lemma row26_roster_safe bound : 200 <= bound -> Forall (source_table_safe bound) row26_roster.
Proof.
  intro Hb. eapply coarse_roster_mono with (lo:=200); [exact Hb|].
  unfold row26_roster. constructor; [exact row26_safe|constructor].
Qed.
Definition row26_q0 := decode_queue Agent8PackedChunk.chunk_data.
Definition row26_remaining := roster_remaining row26_roster (fst row26_q0 ++ snd row26_q0).
Theorem row26_consume bound : 1000006 <= bound ->
  (Forall (source_weighted_safe bound) (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
   Forall (source_weighted_safe bound) row26_remaining).
Proof.
  intro HB. apply roster_checkpoint_consumption.
  - apply row26_roster_safe. lia.
  - exact Agent8PackedChunk.chunk_data_exact.
Qed.
Theorem row26_counts_exact :
  (length (fst row26_q0), length (snd row26_q0),
   length (filter (source_roster_covers row26_roster) (fst row26_q0)),
   length (filter (source_roster_covers row26_roster) (snd row26_q0))) = (156,1,1,0).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions row26_consume.
Print Assumptions row26_counts_exact.
