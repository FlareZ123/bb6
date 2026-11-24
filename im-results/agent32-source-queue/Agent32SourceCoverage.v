From BusyCoq Require Import Enumerate62 Individual62 TC62 CTL62 Eqb Agent32Q0Partition Agent32SourceDrain.
From BusyCoq Require Export Agent32SourceBackwards.
From Coq Require Import List NArith Lia Arith.PeanoNat.
Import ListNotations.
Import TNF_Node.


(* This theorem is about the actual pinned Coq q_0, q_i, MAXT, not a
   different queue implementation. The only remaining semantic
   obligations are local backwards closure and residual certificates. *)
Theorem actual_source_coverage (Safe : T -> Prop) :
  (forall x, match decider (tm x) with
    | TC62.TM.Halt h => Forall Safe (expand' x h) -> Safe x
    | TC62.TM.NonHalt => Safe x
    | TC62.TM.Unknown => True
    end) ->
  (forall i, (i<129)%nat ->
    Forall Safe (snd (SearchQueue_upds decider (q_i (100*i) 100) MAXT))) ->
  Safe node0.
Proof.
  intros Hlocal Hhold.
  assert (Hq0 : safeQ Safe q_0).
  { split.
    - apply Forall_forall; intros x Hx.
      destruct (agent32_q0_chunk_cover x Hx) as [i [Hi Hxi]].
      pose proof (source_updates_backwards Safe decider Hlocal (q_i (100*i) 100)
        MAXT) as Hback.
      assert (Hfinal : safeQ Safe (SearchQueue_upds decider (q_i (100*i) 100) MAXT)).
      { split.
        - rewrite actual_q0_chunk_drains by exact Hi; constructor.
        - apply Hhold; exact Hi. }
      apply Hback in Hfinal.
      exact (proj1 (Forall_forall Safe _) (proj1 Hfinal) x Hxi).
    - rewrite agent32_q0_holdout_empty; constructor. }
  change (safeQ Safe
    (SearchQueue_upds_bfs decider
      (SearchQueue_upds_bfs decider
        (SearchQueue_upds_bfs decider
          (SearchQueue_upds_bfs decider root_1RB))))) in Hq0.
  apply (source_bfs_round_backwards Safe decider Hlocal) in Hq0.
  apply (source_bfs_round_backwards Safe decider Hlocal) in Hq0.
  apply (source_bfs_round_backwards Safe decider Hlocal) in Hq0.
  apply (source_bfs_round_backwards Safe decider Hlocal) in Hq0.
  destruct Hq0 as [Hroot _].
  inversion Hroot; assumption.
Qed.

Print Assumptions actual_source_coverage.
