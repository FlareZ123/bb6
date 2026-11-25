From BusyCoq Require Import Enumerate62 TC62 CTL62 Eqb Agent5Enumerate62DeciderSound
  Agent8SourceWF Agent8AdaptiveSource Agent8WeightedSource Agent8QueueCheckpoint
  Agent32SourceBackwards Individual62.
From Coq Require Import List Lia Arith NArith.
Import ListNotations.
Import TNF_Node.
Open Scope nat_scope.

(* Generalize Agent8's local weighted theorem to independently chosen
   classifiers. The actual TNF fresh-state symmetry and terminal cost
   are unchanged; only the sound classifier interface is abstracted. *)
Theorem source_weighted_local_for
  (f : TC62.TM.TM -> TC62.TM.DecideResult) (budget bound : nat) :
  (budget + 6 <= bound)%nat ->
  (forall t, match f t with
   | TC62.TM.Halt h => exists n, TC62.TM.halts_at t TC62.TM.c0 n h /\ n <= budget
   | TC62.TM.NonHalt => ~ TC62.TM.halts t TC62.TM.c0
   | TC62.TM.Unknown => True
   end) ->
  forall x, match f (tm x) with
  | TC62.TM.Halt h => Forall (source_weighted_safe bound) (expand' x h) ->
      source_weighted_safe bound x
  | TC62.TM.NonHalt => source_weighted_safe bound x
  | TC62.TM.Unknown => True
  end.
Proof.
  intros HB Hsound x.
  pose proof (Hsound (tm x)) as Hspec.
  destruct (f (tm x)) as [h| |] eqn:Edec.
  - intros Hchildren Hg m Hchild n k start Hn Hz Hk.
    destruct Hspec as [n' [Hhalt Hbudget]].
    apply source_halt_transfer in Hhalt.
    destruct h as [q s].
    inversion Hhalt as [t c nn q' l s' r Hrun Hhole]; subst.
    change (tm x (q,s) = None) in Hhole.
    pose proof Hg as [[Hmin Hmax] [Hroot [Hcount Hsup]]].
    assert (Hslot : state_index q < min_unused_state x).
    { eapply (@source_run_support (tm x) (min_unused_state x) n' c0 (q,(l,s,r))).
      - exact Hsup.
      - change (state_index A < min_unused_state x).
        exact (proj1 (Hsup A S0 S1 R B Hroot)).
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


Definition fast_decider (tm0 : TC62.TM.TM) : TC62.TM.DecideResult :=
  match TC_state.decide tm0 [([50]%N,20%nat);([50;100;200]%N,40%nat)] with
  | (TC62.TM.Halt h,_) => TC62.TM.Halt h
  | (TC62.TM.NonHalt,_) => TC62.TM.NonHalt
  | (TC62.TM.Unknown,_) =>
    if decide_nonhalt tm0 (NG 0 1 100 1 0 0 0 false) then TC62.TM.NonHalt
    else if decide_nonhalt tm0 (NG 0 2 200 2 0 0 0 false) then TC62.TM.NonHalt
    else TC62.TM.Unknown
  end.

Lemma fast_decider_sound tm0 :
  match fast_decider tm0 with
  | TC62.TM.Halt h => exists n, TC62.TM.halts_at tm0 TC62.TM.c0 n h /\ n <= N.to_nat 1000000
  | TC62.TM.NonHalt => ~ TC62.TM.halts tm0 TC62.TM.c0
  | TC62.TM.Unknown => True
  end.
Proof.
  unfold fast_decider.
  destruct (TC_state.decide tm0 [([50]%N,20%nat);([50;100;200]%N,40%nat)]) as [r st] eqn:E.
  destruct r.
  - eapply agent32_tc_halt_budget; [exact E|vm_compute; congruence].
  - eapply agent5_tc_nonhalt_sound; exact E.
  - destruct (decide_nonhalt tm0 (NG 0 1 100 1 0 0 0 false)) eqn:E1.
    + eapply agent5_decide_nonhalt_sound; exact E1.
    + destruct (decide_nonhalt tm0 (NG 0 2 200 2 0 0 0 false)) eqn:E2.
      * eapply agent5_decide_nonhalt_sound; exact E2.
      * exact I.
Qed.

Theorem fast_weighted_local bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  forall x, match fast_decider (tm x) with
  | TC62.TM.Halt h => Forall (source_weighted_safe bound) (expand' x h) -> source_weighted_safe bound x
  | TC62.TM.NonHalt => source_weighted_safe bound x
  | TC62.TM.Unknown => True
  end.
Proof.
  intro HB.
  eapply source_weighted_local_for; [exact HB|exact fast_decider_sound].
Qed.

(* Fast continuation of any exact checkpoint, keeping all unknown nodes.
   No assumption that the original and fast classifiers give the same result. *)
Theorem fast_checkpoint_resume bound offset size oldfuel packed newfuel residual :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  SearchQueue_upds decider (q_i offset size) oldfuel = decode_queue packed ->
  SearchQueue_upds fast_decider (decode_queue packed) newfuel = decode_queue residual ->
  safeQ (source_weighted_safe bound) (decode_queue residual) ->
  safeQ (source_weighted_safe bound) (q_i offset size).
Proof.
  intros HB Eold Enew Hres.
  apply (source_updates_backwards _ decider (source_weighted_local bound HB) _ oldfuel).
  rewrite Eold.
  apply (source_updates_backwards _ fast_decider (fast_weighted_local bound HB) _ newfuel).
  rewrite Enew. exact Hres.
Qed.

Lemma checkpoint_decode_canonical p :
  checkpoint_canonicalQ (decode_queue p).
Proof.
  destruct p as [a b]. unfold checkpoint_canonicalQ,decode_queue; cbn [fst snd].
  split; apply Forall_forall; intros x Hx; apply in_map_iff in Hx;
    destruct Hx as [[ [s n] m] [<- _]]; reflexivity.
Qed.

Print Assumptions source_weighted_local_for.
Print Assumptions fast_decider_sound.
Print Assumptions fast_checkpoint_resume.
