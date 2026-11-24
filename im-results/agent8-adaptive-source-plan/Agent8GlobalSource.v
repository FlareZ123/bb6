From BusyCoq Require Import Enumerate62 Agent8WeightedSource Individual62.
From Coq Require Import List Lia Arith NArith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* A zero-writing prefix is preserved with its exact length, not replaced
   by the worst-case five-step correction. *)
Lemma zvisits_zero_path (t : TM) q qs :
  zvisits t q qs ->
  exists r, zero_path t q (List.length qs) r /\ ReachedNZ t r.
Proof.
  intro H. induction H as [q Hq | q d q' qs Hact Htail IH].
  - exists q. split; [constructor|assumption].
  - destruct IH as [r [Hz Hnz]]. exists r. split; [|assumption].
    cbn [List.length]. econstructor; eassumption.
Qed.

Lemma zero_path_run (t : TM) q k r :
  zero_path t q k r -> multistep t k (q,tape0) (r,tape0).
Proof.
  intro H. induction H.
  - constructor.
  - eapply multistep_S; [apply zero_step; eassumption|assumption].
Qed.

(* If the first nonzero write remains in the same state, the machine
   walks a fresh blank ray forever. This excludes both directions. *)
Lemma self_first_write_nonhalt (t : TM) q d :
  t (q,S0) = Some (S1,d,q) -> ~ halts t (q,tape0).
Proof.
  intro H. destruct d.
  - change (~ halts t ((fun r : Stream Sym => (q,(const S0,S0,r))) (const S0))).
    apply progress_nonhalt_simple.
    intro r. exists (S1 >> r).
    eapply progress_intro.
    + pose proof (@step_left t q q S0 S1 (const S0) r H) as Hs.
      rewrite move_left_const in Hs. exact Hs.
    + constructor.
  - change (~ halts t ((fun l : Stream Sym => (q,(l,S0,const S0))) (const S0))).
    apply progress_nonhalt_simple.
    intro l. exists (l << S1).
    eapply progress_intro.
    + pose proof (@step_right t q q S0 S1 l (const S0) H) as Hs.
      rewrite move_right_const in Hs. exact Hs.
    + constructor.
Qed.

Lemma swap_state_injective a b q r :
  swap_state a b q = swap_state a b r -> q = r.
Proof.
  intro H. apply (f_equal (swap_state a b)) in H.
  rewrite !swap_state_involutive in H. exact H.
Qed.

Lemma zero_path_flip (t : TM) q k r :
  zero_path t q k r -> zero_path (flip t) q k r.
Proof.
  intro H. induction H.
  - constructor.
  - eapply zpS with (d:=flip_dir d); [unfold flip; rewrite H; reflexivity|assumption].
Qed.

(* Transfer every halting suffix from its first-write state to a 1RB
   machine by two state transpositions and, if required, tape reflection.
   The incoming zero-path length and actual halting length both survive. *)
Lemma normalize_weighted_suffix bound (t : TM) q r d n k start :
  (forall u : TM, u (A,S0) = Some (S1,R,B) -> weighted_bound bound u) ->
  t (q,S0) = Some (S1,d,r) ->
  q <> r ->
  halts_in t (q,tape0) n ->
  zero_path t start k q ->
  k <= 5 -> (n+k+1 <= bound)%nat.
Proof.
  intros Hnorm Hwrite Hneq Hn Hz Hk.
  set (r1 := swap_state q A r).
  set (t1 := rename_swap t q A).
  assert (Hr1 : r1 <> A).
  { unfold r1. intro E. rewrite <- (swap_state_a q A) in E at 2.
    apply swap_state_injective in E. congruence. }
  assert (HA : swap_state r1 B A = A).
  { apply swap_state_fixed; congruence. }
  pose proof (rename_swap_perm t q A) as HP1.
  change (Perm t t1 (swap_state q A)) in HP1.
  pose proof (@perm_halts_in t t1 (swap_state q A) q tape0 n HP1 Hn) as Hn1.
  rewrite swap_state_a in Hn1.
  pose proof (zero_path_perm t t1 (swap_state q A) start k q HP1 Hz) as Hz1.
  rewrite swap_state_a in Hz1.
  pose proof ((proj2 HP1) q S0 S1 d r Hwrite) as Hw1.
  rewrite swap_state_a in Hw1.
  change (t1 (A,S0) = Some (S1,d,r1)) in Hw1.
  set (t2 := rename_swap t1 r1 B).
  pose proof (rename_swap_perm t1 r1 B) as HP2.
  change (Perm t1 t2 (swap_state r1 B)) in HP2.
  pose proof (@perm_halts_in t1 t2 (swap_state r1 B) A tape0 n HP2 Hn1) as Hn2.
  rewrite HA in Hn2.
  pose proof (zero_path_perm t1 t2 (swap_state r1 B) _ k A HP2 Hz1) as Hz2.
  rewrite HA in Hz2.
  pose proof ((proj2 HP2) A S0 S1 d r1 Hw1) as Hw2.
  rewrite HA,swap_state_a in Hw2.
  destruct d.
  - assert (Hw3 : flip t2 (A,S0) = Some (S1,R,B)).
    { unfold flip. rewrite Hw2. reflexivity. }
    pose proof (flip_halts_in t2 (A,tape0) n Hn2) as Hn3.
    change (halts_in (flip t2) c0 n) in Hn3.
    exact (Hnorm (flip t2) Hw3 n k _ Hn3 (zero_path_flip _ _ _ _ Hz2) Hk).
  - exact (Hnorm t2 Hw2 n k _ Hn2 Hz2 Hk).
Qed.

(* Unrestricted two-symbol source semantics, counting the final halt
   instruction as one step. No fixed additive loss in the bound. *)
Theorem weighted_normalization_global bound :
  6 <= bound ->
  (forall u : TM, u (A,S0) = Some (S1,R,B) -> weighted_bound bound u) ->
  forall t : TM, forall n, halts_in t c0 n -> S n <= bound.
Proof.
  intros Hb Hnorm t n Hn.
  assert (Hhalts : halts t (A,tape0)) by (exists n; exact Hn).
  destruct (halts_zvisits t A Hhalts) as [qs Hvis].
  pose proof (zvisits_bound t A qs Hvis) as Hlen.
  change (List.length qs < 6) in Hlen.
  destruct (zvisits_zero_path t A qs Hvis) as [q [Hz Hnz]].
  pose proof (zero_path_run t A (List.length qs) q Hz) as Hrun.
  assert (Hle : List.length qs <= n) by (eapply within_halt; eassumption).
  pose proof (preceeds_halt t c0 (q,tape0) (List.length qs) n Hn Hrun Hle) as Hsuffix.
  inversion Hnz as [q' Hhalt | q' w d r Hw Hnonzero]; subst.
  - assert (H0 : halts_in t (q,tape0) 0).
    { exists (q,tape0). split; [constructor|exact Hhalt]. }
    pose proof (source_time_unique t (q,tape0) _ _ Hsuffix H0). lia.
  - destruct w; [contradiction|].
    assert (Hneq : q <> r).
    { intro E. subst r. apply (self_first_write_nonhalt t q d Hw).
      exists (n-List.length qs). exact Hsuffix. }
    pose proof (normalize_weighted_suffix bound t q r d
      (n-List.length qs) (List.length qs) A Hnorm Hw Hneq Hsuffix Hz ltac:(lia)).
    lia.
Qed.

Theorem actual_source_global_upper bound plan :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_weighted_safe bound) (adaptive_obligations decider plan q_0) ->
  forall t : TM, forall n, halts_in t c0 n -> S n <= bound.
Proof.
  intros Hmargin Hres.
  apply weighted_normalization_global; [lia|].
  exact (actual_weighted_from_plan bound plan Hmargin Hres).
Qed.

Print Assumptions self_first_write_nonhalt.
Print Assumptions normalize_weighted_suffix.
Print Assumptions weighted_normalization_global.
Print Assumptions actual_source_global_upper.
