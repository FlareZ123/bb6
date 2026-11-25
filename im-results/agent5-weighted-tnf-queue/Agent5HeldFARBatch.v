From BusyCoq Require Import CTL62 Individual62 Enumerate62
  SourceResidualRoster Agent5ChunkCoverage.
From Coq Require Import List Bool NArith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.

(* The parameters below come from the independently accepted Lean block-FAR
   witnesses. The upstream Coq FAR algorithm need not accept the same tables.
   A failed test therefore remains an explicit obligation. *)
Record held_attempt := {
  held_label : string;
  held_table : TM;
  held_flip : bool;
  held_param : DeciderParameter
}.

Definition held_attempts : list held_attempt := [
  Build_held_attempt "0" (TM_from_str "1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RF---_0LA1RA") false
    (RWL_mod_FAR 20000 10000 3 3200 2 4 5 0);
  Build_held_attempt "300" (TM_from_str "1RB0LC_1RC1RE_1LA0LD_0RA0LB_0RF---_0RB1RA") false
    (RWL_mod_FAR 20000 10000 3 3200 2 4 7 0);
  Build_held_attempt "400a" (TM_from_str "1RB---_1RC1RD_0LB0RF_0LE1LD_0LC1LB_0RA0RF") false
    (RWL_mod_FAR 20000 10000 3 3200 2 4 8 0);
  Build_held_attempt "400b" (TM_from_str "1RB1LA_1RC1RD_0LB0RE_0LE0RF_---1LA_1RA1RC") true
    (RWL_mod_FAR 20000 10000 2 3200 2 4 2 0);
  Build_held_attempt "600" (TM_from_str "1RB1LE_1RC0RD_1LB0RE_1RF0LE_0LA0LB_---0RA") true
    (RWL_mod_FAR 20000 10000 2 3200 2 4 2 0);
  Build_held_attempt "700" (TM_from_str "1RB0RA_1RC1LB_1LB0LD_0LE0LD_1RE1LF_---1RA") false
    (RWL_mod_FAR 20000 10000 3 3200 2 4 4 0);
  Build_held_attempt "2700" (TM_from_str "1RB0LD_1LC1RA_1LE1LA_---0RB_1RE0RF_1RF0LC") false
    (RWL_mod_FAR 20000 10000 3 3200 2 4 5 0);
  Build_held_attempt "2800" (TM_from_str "1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---") true
    (RWL_mod_FAR 20000 10000 3 3200 2 4 2 0)
].

Definition held_check (a : held_attempt) : bool :=
  decide_nonhalt
    (if held_flip a then flip (held_table a) else held_table a)
    (held_param a).

Lemma held_check_nonhalt a :
  held_check a = true -> ~ halts (held_table a) c0.
Proof.
  unfold held_check.
  destruct (held_flip a) eqn:Hflip; intro H.
  - assert (Hnonhalt : ~ halts (flip (held_table a)) c0).
    { rewrite halts_halts'. eapply decide_nonhalt_spec. exact H. }
    intros [n Hn]. apply Hnonhalt. exists n.
    pose proof (flip_halts_in (held_table a) c0 n Hn) as Hf.
    change (halts_in (flip (held_table a)) c0 n) in Hf.
    exact Hf.
  - rewrite halts_halts'. eapply decide_nonhalt_spec. exact H.
Qed.

Definition held_certified_roster : list TM :=
  map held_table (filter held_check held_attempts).

Theorem held_certified_roster_safe bound :
  Forall (source_table_safe bound) held_certified_roster.
Proof.
  apply Forall_forall. intros p Hp.
  unfold held_certified_roster in Hp.
  apply in_map_iff in Hp as [a [Heq Hin]].
  subst p. apply filter_In in Hin as [_ Hcheck].
  apply source_nonhalt_cylinder. apply held_check_nonhalt. exact Hcheck.
Qed.

(* This filter preserves every remaining obligation, including every
   unsuccessful FAR attempt. It also consumes refinements of a passed table. *)
Definition held_remaining (xs : list T) : list T :=
  filter (fun x => negb (source_roster_covers held_certified_roster x)) xs.

Theorem held_remaining_safe_iff bound xs :
  Forall (source_weighted_safe bound) xs <->
  Forall (source_weighted_safe bound) (held_remaining xs).
Proof.
  rewrite !Forall_forall.
  split.
  - intros H x Hx. unfold held_remaining in Hx.
    apply filter_In in Hx as [Hin _]. exact (H x Hin).
  - intros H x Hx.
    destruct (source_roster_covers held_certified_roster x) eqn:Hxcover.
    + eapply source_roster_safe.
      * apply held_certified_roster_safe.
      * exact Hxcover.
    + apply H. unfold held_remaining. apply filter_In.
      split; [exact Hx|rewrite Hxcover; reflexivity].
Qed.

Theorem held_filtered_global_upper bound
    (fuel : nat -> N) (packed : nat -> packed_queue)
    (plans : nat -> AdaptivePlan) :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  (forall i, (i < 129)%nat ->
     encode_queue (SearchQueue_upds decider (q_i (100*i) 100) (fuel i)) = packed i) ->
  (forall i, (i < 129)%nat ->
     Forall (source_weighted_safe bound)
       (held_remaining (adaptive_obligations decider (plans i) (decode_queue (packed i))))) ->
  forall t : TM, forall n, halts_in t c0 n -> (S n <= bound)%nat.
Proof.
  intros Hmargin Hpacked Hrest.
  apply (actual_source_chunks_packed_global_upper bound fuel packed plans Hmargin Hpacked).
  intros i Hi. apply (proj2 (held_remaining_safe_iff bound _)).
  exact (Hrest i Hi).
Qed.

Print Assumptions held_check_nonhalt.
Print Assumptions held_certified_roster_safe.
Print Assumptions held_remaining_safe_iff.
Print Assumptions held_filtered_global_upper.
