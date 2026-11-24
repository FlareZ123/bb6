From BusyCoq Require Import Enumerate62 Individual62 TC62 CTL62 Eqb Agent32Q0Partition Agent32SourceDrain.
From Coq Require Import List NArith Lia Arith.PeanoNat.
Import ListNotations.
Import TNF_Node.

Section ActualSourceCoverage.
  Variable Safe : T -> Prop.
  Variable f : TC62.TM.TM -> TC62.TM.DecideResult.

  Definition safeQ (q : SearchQueue) :=
    Forall Safe (fst q) /\ Forall Safe (snd q).

  Hypothesis local_safe : forall x,
    match f (tm x) with
    | TC62.TM.Halt h => Forall Safe (expand' x h) -> Safe x
    | TC62.TM.NonHalt => Safe x
    | TC62.TM.Unknown => True
    end.

  Lemma source_update_backwards q :
    safeQ (get_SQ (SearchQueue_upd f q)) -> safeQ q.
  Proof.
    destruct q as [[|x xs] ys].
    - exact (fun H => H).
    - pose proof (local_safe x) as Hloc.
      cbn [SearchQueue_upd].
      destruct (f (tm x)) as [h| |] eqn:E; cbn [get_SQ safeQ fst snd].
      + intros [Hkids Hys].
        apply Forall_app in Hkids; destruct Hkids as [Hk Hxs].
        split; [constructor; [apply Hloc; exact Hk|exact Hxs]|exact Hys].
      + intros [Hxs Hys].
        split; [constructor; [exact Hloc|exact Hxs]|exact Hys].
      + intros [Hxs Hheld].
        inversion Hheld; subst.
        split; [constructor; assumption|assumption].
  Qed.

  Lemma source_bfs_backwards q :
    safeQ (get_SQ (SearchQueue_upd_bfs f q)) -> safeQ q.
  Proof.
    destruct q as [[|x xs] ys].
    - exact (fun H => H).
    - pose proof (local_safe x) as Hloc.
      cbn [SearchQueue_upd_bfs].
      destruct (f (tm x)) as [h| |] eqn:E; cbn [get_SQ safeQ fst snd].
      + intros [Hxs Hkids].
        apply Forall_app in Hkids; destruct Hkids as [Hk Hys].
        split; [constructor; [apply Hloc; exact Hk|exact Hxs]|exact Hys].
      + intros [Hxs Hys].
        split; [constructor; [exact Hloc|exact Hxs]|exact Hys].
      + intros [Hxs Hheld].
        inversion Hheld; subst.
        split; [constructor; assumption|assumption].
  Qed.

  Lemma source_iter_backwards (g : SearchQueue -> SearchQueue + SearchQueue)
      (Hback : forall q, safeQ (get_SQ (g q)) -> safeQ q) q fuel :
    safeQ (get_SQ (N_iter_until g (inl q) fuel)) -> safeQ q.
  Proof.
    assert (Hinv :
      match N_iter_until g (inl q) fuel with
      | inl s => safeQ s -> safeQ q
      | inr s => safeQ s -> safeQ q
      end).
    { eapply (N_iter_until_spec
        (fun s => safeQ s -> safeQ q)
        (fun s => safeQ s -> safeQ q)).
      - intros x Hx.
        specialize (Hback x).
        destruct (g x) as [y|y] eqn:E;
          intro Hy; apply Hx; apply Hback; exact Hy.
      - exact (fun H => H). }
    destruct (N_iter_until g (inl q) fuel); exact Hinv.
  Qed.

  Lemma source_updates_backwards q fuel :
    safeQ (SearchQueue_upds f q fuel) -> safeQ q.
  Proof.
    unfold SearchQueue_upds.
    apply source_iter_backwards, source_update_backwards.
  Qed.

  Lemma source_bfs_round_backwards q :
    safeQ (SearchQueue_upds_bfs f q) -> safeQ q.
  Proof.
    unfold SearchQueue_upds_bfs.
    intro H.
    apply (source_iter_backwards (SearchQueue_upd_bfs f) source_bfs_backwards q
      (length_tail (fst q))).
    remember (get_SQ (N_iter_until (SearchQueue_upd_bfs f) (inl q)
      (length_tail (fst q)))) as s.
    destruct s as [a b].
    unfold SearchQueue_rst, safeQ in H; cbn [fst snd] in H.
    destruct H as [H _].
    apply Forall_app in H; exact H.
  Qed.
End ActualSourceCoverage.

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
