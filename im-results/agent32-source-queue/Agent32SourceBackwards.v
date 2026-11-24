From BusyCoq Require Import Enumerate62 Individual62 TC62 CTL62 Eqb.
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

Print Assumptions source_updates_backwards.
Print Assumptions source_bfs_round_backwards.
