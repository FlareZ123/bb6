From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5CoarseTree Agent5Row26Data Agent5Row28Data Agent5CoarsePair35 Agent5CoarsePair37 Agent5CoarsePair47 Agent5CoarsePair50.
From BusyCoq Require Agent8PackedChunk.
From Coq Require Import List NArith Bool Lia.
Import ListNotations TNF_Node.
Open Scope nat_scope.

Definition q0_six_roster : list TM :=
  [row26_parent; row28_parent; coarse_tm pair_c_35; coarse_tm pair_c_37;
   coarse_tm pair_c_47; coarse_tm pair_c_50].

Lemma q0_six_roster_safe :
  Forall (source_table_safe 1000006) q0_six_roster.
Proof.
  unfold q0_six_roster.
  constructor.
  - eapply coarse_roster_mono with (lo:=row26_bound).
    + unfold row26_bound. lia.
    + constructor; [exact row26_safe|constructor].
  - constructor.
    + eapply coarse_roster_mono with (lo:=row28_bound).
      * unfold row28_bound. lia.
      * constructor; [exact row28_safe|constructor].
    + constructor.
      * exact pair_safe_35.
      * constructor.
        -- exact pair_safe_37.
        -- constructor.
           ++ exact pair_safe_47.
           ++ constructor.
              ** exact pair_safe_50.
              ** constructor.
Qed.

Definition q0_six_queue := decode_queue Agent8PackedChunk.chunk_data.
Definition q0_six_remaining :=
  roster_remaining q0_six_roster (fst q0_six_queue ++ snd q0_six_queue).

Theorem q0_six_consume bound : 1000006 <= bound ->
  (Forall (source_weighted_safe bound)
    (adaptive_obligations decider (AP_advance 1000000%N AP_stop) (q_i 0 100)) <->
   Forall (source_weighted_safe bound) q0_six_remaining).
Proof.
  intro HB. apply roster_checkpoint_consumption.
  - eapply coarse_roster_mono with (lo:=1000006); [exact HB|].
    exact q0_six_roster_safe.
  - exact Agent8PackedChunk.chunk_data_exact.
Qed.

Theorem q0_six_counts_exact :
  (length (fst q0_six_queue), length (snd q0_six_queue),
   length (filter (source_roster_covers q0_six_roster) (fst q0_six_queue)),
   length (filter (source_roster_covers q0_six_roster) (snd q0_six_queue))) = (156,1,6,0).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions q0_six_roster_safe.
Print Assumptions q0_six_consume.
Print Assumptions q0_six_counts_exact.
