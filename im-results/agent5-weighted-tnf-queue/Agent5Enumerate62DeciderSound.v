From BusyCoq Require Import Enumerate62 Individual62 CTL62 TC62.

From Coq Require Import NArith Lia.
Import TNF_Node.

Lemma agent5_tc_halt_sound (tm0 : TM) ls h st :
  TC_state.decide tm0 ls = (Halt h, st) ->
  exists n', halts_at tm0 c0 n' h.
Proof.
  intro Hdec.
  pose proof (TC_state_decide_spec tm0 ls) as Hspec.
  rewrite Hdec in Hspec.
  simpl in Hspec.
  destruct Hspec as [n' [Hhalt _]].
  exists n'.
  exact Hhalt.
Qed.

Lemma agent5_tc_nonhalt_sound (tm0 : TM) ls st :
  TC_state.decide tm0 ls = (NonHalt, st) ->
  ~ halts tm0 c0.
Proof.
  intro Hdec.
  pose proof (TC_state_decide_spec tm0 ls) as Hspec.
  rewrite Hdec in Hspec.
  exact Hspec.
Qed.

Lemma agent5_halts_alias (tm0 : TM) :
  DHTMFromTM.TM.halts tm0 DHTMFromTM.TM.c0 <-> halts tm0 c0.
Proof.
  rewrite DHTMFromTM.TM.halts_halts', halts_halts'.
  (* The two generative TM functors have distinct relational constructors,
     but the transparent executable step and multistep definitions agree. *)
  reflexivity.
Qed.

Lemma agent5_decide_nonhalt_sound (tm0 : TM) arg :
  decide_nonhalt tm0 arg = true ->
  ~ halts tm0 c0.
Proof.
  intro H.
  pose proof (decide_nonhalt_spec tm0 arg H) as Hn.
  rewrite <- DHTMFromTM.TM.halts_halts' in Hn.
  intro Hhalts.
  apply Hn.
  exact (proj2 (agent5_halts_alias tm0) Hhalts).
Qed.

Theorem agent5_decider_sound (tm0 : TM) :
  match TNF_Node.decider tm0 with
  | Halt h => exists n', halts_at tm0 c0 n' h
  | NonHalt => ~ halts tm0 c0
  | Unknown => True
  end.
Proof.
  unfold TNF_Node.decider.
  repeat match goal with
  | |- context [TC_state.decide tm0 ?ls] =>
      let result := fresh "res" in
      let state := fresh "st" in
      let E := fresh "Etc" in
      destruct (TC_state.decide tm0 ls) as [result state] eqn:E;
      destruct result
  | |- context [decide_nonhalt tm0 ?arg] =>
      destruct (decide_nonhalt tm0 arg) eqn:?
  end.
  all: simpl.
  all: try solve [eapply agent5_tc_halt_sound; eassumption].
  all: try solve [eapply agent5_tc_nonhalt_sound; eassumption].
  all: try solve [eapply agent5_decide_nonhalt_sound; eassumption].
  all: exact I.
Qed.

Print Assumptions agent5_decider_sound.

(* Agent 32: retain the primitive budget in the source theorem. *)
Lemma agent32_tc_halt_budget (tm0 : TM) ls h st :
  TC_state.decide tm0 ls = (Halt h, st) ->
  (N_list_sum (map N_list_sum (map fst ls)) <= 1000000)%N ->
  exists n', halts_at tm0 c0 n' h /\ (n' <= N.to_nat 1000000)%nat.
Proof.
  intros Hdec Hbudget.
  pose proof (TC_state_decide_spec tm0 ls) as Hspec.
  rewrite Hdec in Hspec.
  destruct Hspec as [n' [Hhalt Hbound]].
  exists n'; split; [exact Hhalt|].
  apply N2Nat.inj_le in Hbudget.
  eapply Nat.le_trans; eassumption.
Qed.

Theorem agent32_decider_bounded_sound (tm0 : TM) :
  match TNF_Node.decider tm0 with
  | Halt h => exists n', halts_at tm0 c0 n' h /\ (n' <= N.to_nat 1000000)%nat
  | NonHalt => ~ halts tm0 c0
  | Unknown => True
  end.
Proof.
  unfold TNF_Node.decider.
  repeat match goal with
  | |- context [TC_state.decide tm0 ?ls] =>
      let result := fresh "res" in
      let state := fresh "st" in
      let E := fresh "Etc" in
      destruct (TC_state.decide tm0 ls) as [result state] eqn:E;
      destruct result
  | |- context [decide_nonhalt tm0 ?arg] =>
      destruct (decide_nonhalt tm0 arg) eqn:?
  end.
  all: try solve [eapply agent32_tc_halt_budget; [eassumption|vm_compute; congruence]].
  all: try solve [eapply agent5_tc_nonhalt_sound; eassumption].
  all: try solve [eapply agent5_decide_nonhalt_sound; eassumption].
  all: exact I.
Qed.

Print Assumptions agent32_decider_bounded_sound.
