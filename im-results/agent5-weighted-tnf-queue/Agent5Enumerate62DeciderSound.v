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
  lia.
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

(* Agent 32: concrete finite-list interface to the Lean source classifier.
   Reuse Individual62.cconfig_step itself, rather than copying the simulator. *)
Lemma agent32_cconfig_step_commute (tm0 : TM) (x : cconfig) :
  step_c tm0 (cconfig_to_config x) =
  option_map cconfig_to_config (cconfig_step tm0 x).
Proof.
  destruct x as [[[l r] m] q].
  cbn [cconfig_to_config step_c cconfig_step].
  destruct (tm0 (q,m)) as [[[w d] s]|] eqn:E; [|reflexivity].
  destruct d; [destruct l|destruct r]; reflexivity.
Qed.

Fixpoint agent32_finiteRun (tm0 : TM) (n : nat) (x : cconfig) : option cconfig :=
  match n with
  | O => Some x
  | S k => match cconfig_step tm0 x with
           | None => None
           | Some y => agent32_finiteRun tm0 k y
           end
  end.

Lemma agent32_cconfig_run_commute (tm0 : TM) (n : nat) (x : cconfig) :
  multistep_c tm0 n (cconfig_to_config x) =
  option_map cconfig_to_config (agent32_finiteRun tm0 n x).
Proof.
  revert x; induction n as [|n IH]; intros x; [reflexivity|].
  cbn [multistep_c agent32_finiteRun].
  rewrite agent32_cconfig_step_commute.
  destruct (cconfig_step tm0 x) as [y|]; cbn; [apply IH|reflexivity].
Qed.

Definition agent32_finiteBlank : cconfig := (nil,nil,s0,q0).
Definition agent32_query (x : cconfig) : Q*Sym :=
  match x with (_,_,m,q) => (q,m) end.

Lemma agent32_finiteBlank_correct :
  cconfig_to_config agent32_finiteBlank = c0.
Proof. reflexivity. Qed.

Lemma agent32_halts_at_finite (tm0 : TM) n h :
  halts_at tm0 c0 n h ->
  exists x, agent32_finiteRun tm0 n agent32_finiteBlank = Some x /\
    agent32_query x = h /\ tm0 h = None.
Proof.
  intros H.
  inversion H as [tm' c n' q l m r Hrun Hhalt]; subst.
  apply <- multistep_c_spec in Hrun.
  pose proof (agent32_cconfig_run_commute tm0 n agent32_finiteBlank) as HC.
  rewrite agent32_finiteBlank_correct, Hrun in HC.
  destruct (agent32_finiteRun tm0 n agent32_finiteBlank) as [x|] eqn:E; [|discriminate].
  exists x; split; [reflexivity|].
  destruct x as [[[ll rr] mm] qq].
  cbn [option_map cconfig_to_config agent32_query] in HC.
  inversion HC; subst.
  split; [reflexivity|exact Hhalt].
Qed.

Lemma agent32_nonhalt_finite (tm0 : TM) :
  ~ halts tm0 c0 ->
  forall n, exists x, agent32_finiteRun tm0 n agent32_finiteBlank = Some x.
Proof.
  intros H n.
  destruct ((proj1 nonhalt_iff H) n) as [c Hrun].
  apply <- multistep_c_spec in Hrun.
  pose proof (agent32_cconfig_run_commute tm0 n agent32_finiteBlank) as HC.
  rewrite agent32_finiteBlank_correct,Hrun in HC.
  destruct (agent32_finiteRun tm0 n agent32_finiteBlank); [eexists; reflexivity|discriminate].
Qed.

Theorem agent32_decider_finite_sound (tm0 : TM) :
  match TNF_Node.decider tm0 with
  | Halt h => exists n x, (n <= N.to_nat 1000000)%nat /\
      agent32_finiteRun tm0 n agent32_finiteBlank = Some x /\
      agent32_query x = h /\ tm0 h = None
  | NonHalt => forall n, exists x, agent32_finiteRun tm0 n agent32_finiteBlank = Some x
  | Unknown => True
  end.
Proof.
  pose proof (agent32_decider_bounded_sound tm0) as H.
  destruct (TNF_Node.decider tm0) as [h| |].
  - destruct H as [n [Hhalt Hbudget]].
    destruct (agent32_halts_at_finite tm0 n h Hhalt) as [x Hx].
    exists n,x; auto.
  - apply agent32_nonhalt_finite; exact H.
  - exact I.
Qed.

Print Assumptions agent32_decider_finite_sound.
