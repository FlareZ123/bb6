From BusyCoq Require Import Enumerate62 Individual62 TC62 CTL62 Eqb Agent32Q0Partition Agent32SourceDrain Agent32SourceCoverage.
From Coq Require Import List NArith.
Import ListNotations.
Import TNF_Node.

(* The schedule is independent of any historical holdout roster. *)
Inductive AdaptivePlan : Type :=
| AP_stop
| AP_advance (fuel : N) (next : AdaptivePlan)
| AP_split (n : nat) (left right : AdaptivePlan).

(* All nodes remaining at a stop are explicit obligations, whether active
   or already held. Split partitions only the actual active list, keeping
   the held list exactly once. No equality of output order is presumed. *)
Fixpoint adaptive_obligations
    (f : TC62.TM.TM -> TC62.TM.DecideResult) (plan : AdaptivePlan) (q : SearchQueue) : list T :=
  match plan with
  | AP_stop => fst q ++ snd q
  | AP_advance fuel next =>
      adaptive_obligations f next (SearchQueue_upds f q fuel)
  | AP_split n left right =>
      snd q ++
        (adaptive_obligations f left (firstn n (fst q), []) ++
         adaptive_obligations f right (skipn n (fst q), []))
  end.

Section AdaptiveCoverage.
  Variable Safe : T -> Prop.
  Variable f : TC62.TM.TM -> TC62.TM.DecideResult.
  Hypothesis Hlocal : forall x,
    match f (tm x) with
    | TC62.TM.Halt h => Forall Safe (expand' x h) -> Safe x
    | TC62.TM.NonHalt => Safe x
    | TC62.TM.Unknown => True
    end.

  Theorem adaptive_plan_sound plan q :
    Forall Safe (adaptive_obligations f plan q) -> safeQ Safe q.
  Proof.
    revert q.
    induction plan as [|fuel next IH|n left IHleft right IHright];
      intros q H; cbn [adaptive_obligations] in H.
    - unfold safeQ. apply Forall_app in H. exact H.
    - apply (source_updates_backwards Safe f Hlocal q fuel).
      apply IH. exact H.
    - apply Forall_app in H. destruct H as [Hheld Hbranches].
      apply Forall_app in Hbranches. destruct Hbranches as [Hl Hr].
      pose proof (IHleft _ Hl) as Hleft.
      pose proof (IHright _ Hr) as Hright.
      unfold safeQ in Hleft, Hright |- *.
      cbn [fst snd] in Hleft, Hright.
      split; [|exact Hheld].
      rewrite <- (firstn_skipn n (fst q)).
      apply Forall_app. split; [exact (proj1 Hleft)|exact (proj1 Hright)].
  Qed.

  (* A worker can preserve an exact checkpoint equation once, then finish
     its continuation separately. A digest alone is not such an equation. *)
  Theorem adaptive_checkpoint_sound q fuel q' plan :
    SearchQueue_upds f q fuel = q' ->
    Forall Safe (adaptive_obligations f plan q') ->
    safeQ Safe q.
  Proof.
    intros E H.
    apply (source_updates_backwards Safe f Hlocal q fuel).
    rewrite E. apply (adaptive_plan_sound plan q'). exact H.
  Qed.
End AdaptiveCoverage.

(* Directly use the actual pinned source q_0, without requiring every
   independently scheduled job to run to MAXT. *)
Theorem actual_source_adaptive_coverage (Safe : T -> Prop) (plan : AdaptivePlan) :
  (forall x, match decider (tm x) with
    | TC62.TM.Halt h => Forall Safe (expand' x h) -> Safe x
    | TC62.TM.NonHalt => Safe x
    | TC62.TM.Unknown => True
    end) ->
  Forall Safe (adaptive_obligations decider plan q_0) ->
  Safe node0.
Proof.
  intros Hlocal Hres.
  pose proof (adaptive_plan_sound Safe decider Hlocal plan q_0 Hres) as Hq0.
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

Print Assumptions adaptive_plan_sound.
Print Assumptions adaptive_checkpoint_sound.
Print Assumptions actual_source_adaptive_coverage.
