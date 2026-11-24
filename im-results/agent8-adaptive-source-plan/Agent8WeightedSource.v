From BusyCoq Require Import Enumerate62 TC62 Eqb Agent5Enumerate62DeciderSound
  Agent8SourceWF Agent8AdaptiveSource Individual62.
From BusyCoq Require Export Agent8ZeroDelay.
From Coq Require Import List Lia NArith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* Use the original Individual62 relations and source Permute/Enumerate
   lemmas. TC62 has generative copies of the relational constructors; its
   executable multistep is definitionally the same. *)
Lemma source_halt_transfer (t : TM) h n :
  TC62.TM.halts_at t TC62.TM.c0 n h ->
  halts_at t c0 n h.
Proof.
  intro H. inversion H as [tt c nn q l m r Hrun Hhalt]; subst.
  (* TC62's halts_at gives a relational run. Bridge through its executable
     evaluator before transporting to Individual62's relational copy. *)
  apply <- TC62.TM.multistep_c_spec in Hrun.
  change (multistep_c t n c0 = Some (q,(l,m,r))) in Hrun.
  apply multistep_c_spec in Hrun.
  econstructor.
  - exact Hrun.
  - exact Hhalt.
Qed.

Lemma source_nonhalt_transfer (t : TM) :
  ~ TC62.TM.halts t TC62.TM.c0 -> ~ halts t c0.
Proof. rewrite TC62.TM.halts_halts', halts_halts'. exact (fun h => h). Qed.

Lemma source_run_support (t : TM) cut n c c' :
  source_support t cut ->
  state_index (fst c) < cut ->
  multistep t n c c' ->
  state_index (fst c') < cut.
Proof.
  intros Hsup Hstart Hrun. induction Hrun.
  - exact Hstart.
  - apply IHHrun. inversion H; subst; cbn [fst];
      match goal with
      | E : t (?q,?s) = Some (?w,?d,?q') |- _ =>
          exact (proj2 (Hsup q s w d q' E))
      end.
Qed.

Lemma source_time_unique t c n k :
  halts_in t c n -> halts_in t c k -> n = k.
Proof.
  intros Hn Hk.
  destruct Hn as [cn [Hrn Hhn]].
  destruct Hk as [ck [Hrk Hhk]].
  assert (E1 : n <= k).
  { eapply within_halt; [exists ck; split; eassumption|exact Hrn]. }
  assert (E2 : k <= n).
  { eapply within_halt; [exists cn; split; eassumption|exact Hrk]. }
  lia.
Qed.

Lemma source_total_nonhalt (t : TM) :
  (forall h, t h <> None) -> ~ halts t c0.
Proof.
  intros H [n [[q [[l s] r]] [Hrun Hhalt]]].
  exact (H (q,s) Hhalt).
Qed.

(* The exact weight is the zero-writing delay of the concrete completion.
   No assumption that the delay is zero on a long-running machine. *)
(* zero_path is defined and checked in Agent8ZeroDelay. *)

Definition weighted_bound (bound : nat) (t : TM) : Prop :=
  forall n k s, halts_in t c0 n -> zero_path t s k A ->
    k <= 5 -> (n+k+1 <= bound)%nat.

Lemma zero_path_perm (t u : TM) (f : Q -> Q) q k r :
  Perm t u f -> zero_path t q k r -> zero_path u (f q) k (f r).
Proof.
  intros Hp Hz. induction Hz.
  - constructor.
  - econstructor; [eapply (proj2 Hp); eassumption|exact IHHz].
Qed.

Lemma weighted_perm_back (bound : nat) (t u : TM) f :
  Perm t u f -> f A = A ->
  weighted_bound bound u -> weighted_bound bound t.
Proof.
  intros Hp Hfix Hu n k s Hn Hz Hk.
  apply (Hu n k (f s)); [| |exact Hk].
  - pose proof (@perm_halts_in t u f A tape0 n Hp Hn) as H.
    rewrite Hfix in H. exact H.
  - pose proof (zero_path_perm t u f s k A Hp Hz) as H.
    rewrite Hfix in H. exact H.
Qed.

Definition swap_state (a b q : Q) : Q :=
  if eqb_q q a then b else if eqb_q q b then a else q.

Lemma swap_state_involutive a b q : swap_state a b (swap_state a b q) = q.
Proof. destruct a,b,q; reflexivity. Qed.

Lemma swap_state_a a b : swap_state a b a = b.
Proof. destruct a,b; reflexivity. Qed.

Lemma swap_state_fixed a b q :
  q <> a -> q <> b -> swap_state a b q = q.
Proof.
  intros H1 H2. unfold swap_state.
  destruct (eqb_q q a), (eqb_q q b); congruence.
Qed.

Definition rename_swap (t : TM) a b : TM :=
  fun '(q,s) => option_map (fun '(w,d,r) => (w,d,swap_state a b r))
    (t (swap_state a b q,s)).

Lemma rename_swap_perm (t : TM) a b :
  Perm t (rename_swap t a b) (swap_state a b).
Proof.
  split.
  - intros q s H. unfold rename_swap. rewrite swap_state_involutive,H. reflexivity.
  - intros q s w d r H. unfold rename_swap. rewrite swap_state_involutive,H. reflexivity.
Qed.

Lemma swap_fixed_below a b q cut :
  state_index q < cut -> cut <= state_index a -> cut <= state_index b ->
  swap_state a b q = q.
Proof.
  intros Hq Ha Hb. apply swap_state_fixed; intro E; subst q; lia.
Qed.

Lemma rename_child (m t : TM) cut a b :
  source_support t cut -> cut <= state_index a -> cut <= state_index b ->
  is_child_of m t -> is_child_of (rename_swap m a b) t.
Proof.
  intros Hsup Ha Hb Hchild [q s].
  destruct (t (q,s)) as [[[w d] r]|] eqn:E; [right|left; reflexivity].
  destruct (Hsup q s w d r E) as [Hq Hr].
  destruct (Hchild (q,s)) as [Hbad|Hm]; [congruence|].
  unfold rename_swap.
  rewrite (swap_fixed_below a b q cut Hq Ha Hb), Hm, E.
  cbn [option_map].
  rewrite (swap_fixed_below a b r cut Hr Ha Hb).
  reflexivity.
Qed.

Lemma completion_refine (m t : TM) h v :
  is_child_of m t -> m h = Some v ->
  is_child_of m (tm_upd t h v).
Proof.
  intros Hchild Hact k.
  destruct (BusyCoq.Eqb.eqb_spec k h) as [E|E].
  - subst k. right. rewrite source_upd_hit. exact Hact.
  - rewrite source_upd_miss by exact E. exact (Hchild k).
Qed.

Definition source_weighted_safe (bound : nat) (x : T) : Prop :=
  source_good x -> forall t, is_child_of t (tm x) -> weighted_bound bound t.

(* All three actual classifier outcomes, with source-native exact metadata,
   and the real fresh-state child selection. The halt branch receives its
   terminal query and primitive transition bound from Agent32's theorem. *)
Theorem source_weighted_local bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  forall x, match decider (tm x) with
  | TC62.TM.Halt h => Forall (source_weighted_safe bound) (expand' x h) ->
      source_weighted_safe bound x
  | TC62.TM.NonHalt => source_weighted_safe bound x
  | TC62.TM.Unknown => True
  end.
Proof.
  intros HB x.
  pose proof (agent32_decider_bounded_sound (tm x)) as Hspec.
  destruct (decider (tm x)) as [h| |] eqn:Edec.
  - intros Hchildren Hg m Hchild n k start Hn Hz Hk.
    destruct Hspec as [n' [Hhalt Hbudget]].
    apply source_halt_transfer in Hhalt.
    destruct h as [q s].
    inversion Hhalt as [t c nn q' l s' r Hrun Hhole]; subst.
    change (tm x (q,s) = None) in Hhole.
    pose proof Hg as [[Hmin Hmax] [Hroot [Hcount Hsup]]].
    assert (Hslot : state_index q < min_unused_state x).
    { eapply (source_run_support (t:=tm x) (cut:=min_unused_state x)
        (n:=n') (c:=c0) (c':=(q,(l,s,r)))).
      - exact Hsup.
      - cbn [c0 fst state_index]. lia.
      - exact Hrun. }
    destruct (m (q,s)) as [[[w d] dst]|] eqn:Eact.
    + destruct (Nat.eq_dec (num_undef_trans x) 1) as [Hlast|Hnot].
      * exfalso. apply (source_total_nonhalt m); [|exists n; exact Hn].
        intros h Hnone.
        destruct (BusyCoq.Eqb.eqb_spec h (q,s)) as [E|E]; [subst h; congruence|].
        assert (Hcnt : get_num_undef_trans (tm x) = 1) by lia.
        pose proof (source_count_one (tm x) (q,s) Hcnt Hhole h E) as Hother.
        destruct (Hchild h); congruence.
      * rewrite source_expand'_nonlast in Hchildren by exact Hnot.
        pose proof (source_expand_good x (q,s) Hg Hhole Hslot) as Hgoodchildren.
        rewrite Forall_forall in Hchildren,Hgoodchildren.
        destruct (Nat.lt_ge_cases (state_index dst) (min_unused_state x)) as [Hold|Hnew].
        -- pose proof (source_expand_old_member x (q,s) w d dst Hold) as Hmem.
           exact (Hchildren _ Hmem (Hgoodchildren _ Hmem) m
             (completion_refine m (tm x) (q,s) (w,d,dst) Hchild Eact)
             n k start Hn Hz Hk).
        -- assert (Hlt : min_unused_state x < 6).
           { pose proof (state_index_bound dst). lia. }
           destruct (fresh_state_exists _ Hlt) as [fresh [rest [Hskip Hfresh]]].
           pose proof (source_expand_fresh_member x (q,s) w d fresh rest Hskip) as Hmem.
           assert (Hfreshge : min_unused_state x <= state_index fresh) by lia.
           assert (Hren : is_child_of (rename_swap m dst fresh) (tm x)).
           { eapply rename_child; eassumption. }
           assert (Hact : rename_swap m dst fresh (q,s) = Some (w,d,fresh)).
           { unfold rename_swap.
             rewrite (swap_fixed_below dst fresh q _ Hslot Hnew Hfreshge), Eact.
             cbn [option_map]. rewrite swap_state_a. reflexivity. }
           assert (Hfix : swap_state dst fresh A = A).
           { apply (swap_fixed_below dst fresh A (min_unused_state x)); [cbn [state_index]; lia|assumption|assumption]. }
           assert (Hweighted : weighted_bound bound (rename_swap m dst fresh)).
           { exact (Hchildren _ Hmem (Hgoodchildren _ Hmem) _
                 (completion_refine _ (tm x) (q,s) (w,d,fresh) Hren Hact)). }
           exact (weighted_perm_back bound m (rename_swap m dst fresh) _
             (rename_swap_perm m dst fresh) Hfix Hweighted n k start Hn Hz Hk).
    + assert (Hnm : halts_in m c0 n').
      { exists (q,(l,s,r)). split.
        - eapply child_multistep; eassumption.
        - exact Eact. }
      pose proof (source_time_unique m c0 n n' Hn Hnm). lia.
  - intros Hg m Hchild n k start Hn Hz Hk.
    exfalso. apply (child_nonhalt m (tm x) c0 Hchild (source_nonhalt_transfer _ Hspec)).
    exists n. exact Hn.
  - exact I.
Qed.

Lemma source_root_child (t : TM) :
  t (A,S0) = Some (S1,R,B) -> is_child_of t (tm node0).
Proof.
  intros H [q s]. destruct q,s; cbn [node0 tm TM_from_str];
    try (left; reflexivity); right; exact H.
Qed.

Theorem actual_weighted_from_plan bound plan :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_weighted_safe bound) (adaptive_obligations decider plan q_0) ->
  forall t : TM, t (A,S0) = Some (S1,R,B) -> weighted_bound bound t.
Proof.
  intros HB Hres t Hroot.
  pose proof (actual_source_adaptive_coverage (source_weighted_safe bound)
    plan (source_weighted_local bound HB) Hres) as Hsafe.
  exact (Hsafe source_root_good t (source_root_child t Hroot)).
Qed.

Print Assumptions source_halt_transfer.
Print Assumptions source_nonhalt_transfer.
Print Assumptions weighted_perm_back.
Print Assumptions source_weighted_local.
Print Assumptions actual_weighted_from_plan.
