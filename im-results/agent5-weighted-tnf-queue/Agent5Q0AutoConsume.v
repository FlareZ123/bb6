From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5CoarseTree Agent5Q0AutoData.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List NArith Bool Lia.
Import ListNotations TNF_Node.
Open Scope nat_scope.

Definition q0_auto_roster : list TM := [auto_parent].
Lemma q0_auto_roster_safe : Forall (source_table_safe auto_bound) q0_auto_roster.
Proof. constructor; [exact auto_parent_safe|constructor]. Qed.
Definition q0_auto_queue := decode_queue Agent8PackedChunk.chunk_data.
Definition q0_auto_remaining :=
  roster_remaining q0_auto_roster (fst q0_auto_queue ++ snd q0_auto_queue).
Theorem q0_auto_consume bound : auto_bound <= bound ->
  (Forall (source_weighted_safe bound)
    (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
   Forall (source_weighted_safe bound) q0_auto_remaining).
Proof.
  intro HB. apply roster_checkpoint_consumption.
  - eapply coarse_roster_mono with (lo:=auto_bound); [exact HB|exact q0_auto_roster_safe].
  - exact Agent8PackedChunk.chunk_data_exact.
Qed.
Theorem q0_auto_counts_exact :
  (length (fst q0_auto_queue), length (snd q0_auto_queue),
   length (filter (source_roster_covers q0_auto_roster) (fst q0_auto_queue)),
   length (filter (source_roster_covers q0_auto_roster) (snd q0_auto_queue))) = (156,1,1,0).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions q0_auto_consume.
Print Assumptions q0_auto_counts_exact.
