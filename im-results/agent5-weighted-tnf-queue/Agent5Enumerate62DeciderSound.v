From BusyCoq Require Import Enumerate62.

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

Lemma agent5_decide_nonhalt_sound (tm0 : TM) arg :
  decide_nonhalt tm0 arg = true ->
  ~ halts tm0 c0.
Proof.
  intro H.
  eapply decide_nonhalt_spec.
  exact H.
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
      destruct (TC_state.decide tm0 ls) as [[h| |] st] eqn:?
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
