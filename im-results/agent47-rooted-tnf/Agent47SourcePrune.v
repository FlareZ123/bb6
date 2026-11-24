From BusyCoq Require Import SourceResidualRoster Agent47SourceWitness
  Agent32SourceBackwards Agent8WeightedSource Agent8GlobalSource
  Enumerate62 Individual62 Eqb.
From Coq Require Import List Bool NArith Lia.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* A certified bounded-halting cylinder need not be nonhalting.
   It is removed as Safe, never falsely returned as a NonHalt verdict. *)
Definition source_prune_update (roster : list TM) (q : SearchQueue) :
  SearchQueue + SearchQueue :=
  match fst q with
  | [] => inr q
  | x::xs =>
      if source_roster_covers roster x then inl (xs,snd q)
      else SearchQueue_upd decider q
  end.

Definition source_prune_updates roster q fuel :=
  get_SQ (N_iter_until (source_prune_update roster) (inl q) fuel).

Theorem source_prune_backwards bound roster :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) roster ->
  forall q,
    safeQ (source_weighted_safe bound) (get_SQ (source_prune_update roster q)) ->
    safeQ (source_weighted_safe bound) q.
Proof.
  intros HB Hroster [[|x xs] ys] H.
  - exact H.
  - unfold source_prune_update in H. cbn [fst snd] in H.
    destruct (source_roster_covers roster x) eqn:E.
    + change (Forall (source_weighted_safe bound) xs /\
              Forall (source_weighted_safe bound) ys) in H.
      destruct H as [Hx Hy]. split; [constructor|exact Hy].
      * eapply source_roster_safe; eassumption.
      * exact Hx.
    + eapply (source_update_backwards (source_weighted_safe bound)
        decider (source_weighted_local bound HB)).
      exact H.
Qed.

Theorem source_prune_updates_backwards bound roster q fuel :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) roster ->
  safeQ (source_weighted_safe bound) (source_prune_updates roster q fuel) ->
  safeQ (source_weighted_safe bound) q.
Proof.
  intros HB Hroster.
  unfold source_prune_updates.
  apply (source_iter_backwards (source_weighted_safe bound)
    (source_prune_update roster)).
  apply source_prune_backwards; assumption.
Qed.

(* This is useful for a literal certified checkpoint without requiring
   equality to the unpruned future queue or any historical roster. *)
Theorem source_prune_checkpoint_sound bound roster q fuel residual :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_table_safe bound) roster ->
  source_prune_updates roster q fuel = residual ->
  Forall (source_weighted_safe bound) (fst residual ++ snd residual) ->
  safeQ (source_weighted_safe bound) q.
Proof.
  intros HB Hr E Hres.
  apply (source_prune_updates_backwards bound roster q fuel HB Hr).
  rewrite E. unfold safeQ. apply Forall_app in Hres. exact Hres.
Qed.

Print Assumptions source_prune_backwards.
Print Assumptions source_prune_updates_backwards.
Print Assumptions source_prune_checkpoint_sound.
