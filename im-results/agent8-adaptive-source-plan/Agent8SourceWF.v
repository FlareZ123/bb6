From BusyCoq Require Import Enumerate62 Individual62 TC62 Eqb.
From Coq Require Import List Lia NArith Arith.
Import ListNotations.
Import TNF_Node.

(* Actual-source metadata invariant, independent of the abstract Lean queue. *)
Definition state_index (q : Q) : nat :=
  match q with A => 0 | B => 1 | C => 2 | D => 3 | E => 4 | F => 5 end.

Lemma state_index_bound q : state_index q < 6.
Proof. destruct q; cbn [state_index]; lia. Qed.

Lemma state_index_injective q r : state_index q = state_index r -> q = r.
Proof. destruct q,r; cbn [state_index]; congruence. Qed.

Lemma state_in_prefix cut q :
  In q (firstn cut all_qs) <-> state_index q < cut.
Proof.
  destruct q; destruct cut as [|[|[|[|[|[|cut]]]]]];
    cbn [all_qs BB62.all_qs state_index firstn In];
    intuition congruence || lia.
Qed.

Lemma fresh_state_index cut q qs :
  skipn cut all_qs = q::qs -> state_index q = cut /\ cut < 6.
Proof.
  destruct cut as [|[|[|[|[|[|cut]]]]]]; intro H;
    cbn [all_qs BB62.all_qs skipn] in H;
    try (inversion H; subst; cbn [state_index]; lia).
  rewrite skipn_nil in H. discriminate.
Qed.

Lemma fresh_state_exists cut :
  cut < 6 -> exists q qs, skipn cut all_qs = q::qs /\ state_index q = cut.
Proof.
  destruct cut as [|[|[|[|[|[|cut]]]]]]; intro H;
    try (do 2 eexists; split; reflexivity).
  lia.
Qed.

Lemma source_upd_hit (t : TM) h v :
  tm_upd t h v h = Some v.
Proof.
  unfold tm_upd. rewrite tm_simpl_spec'.
  destruct (BusyCoq.Eqb.eqb_spec h h); congruence.
Qed.

Lemma source_upd_miss (t : TM) h v k :
  k <> h -> tm_upd t h v k = t k.
Proof.
  intro H. unfold tm_upd. rewrite tm_simpl_spec'.
  destruct (BusyCoq.Eqb.eqb_spec k h); congruence.
Qed.

(* Counting holes in the actual source order, by twelve finite slots. *)
Definition hole_value (o : option (Sym*dir*Q)) : nat :=
  match o with None => 1 | Some _ => 0 end.

Lemma hole_value_bound o : hole_value o <= 1.
Proof. destruct o; cbn [hole_value]; lia. Qed.

Lemma source_count_formula t :
  get_num_undef_trans t =
  (hole_value (t (A,S0)) + hole_value (t (A,S1)) +
   hole_value (t (B,S0)) + hole_value (t (B,S1)) +
   hole_value (t (C,S0)) + hole_value (t (C,S1)) +
   hole_value (t (D,S0)) + hole_value (t (D,S1)) +
   hole_value (t (E,S0)) + hole_value (t (E,S1)) +
   hole_value (t (F,S0)) + hole_value (t (F,S1)))%nat.
Proof.
  unfold get_num_undef_trans, Nat_sum, hole_value.
  cbn [all_qs all_syms BB62.all_qs BB62.all_syms map fold_right Nat_sum].
  repeat rewrite Nat.add_0_r.
  lia.
Qed.

Lemma source_count_update t h v :
  t h = None ->
  S (get_num_undef_trans (tm_upd t h v)) = get_num_undef_trans t.
Proof.
  intro H.
  rewrite !source_count_formula.
  destruct h as [q s]; destruct q,s;
    repeat (rewrite source_upd_hit || rewrite source_upd_miss by discriminate);
    rewrite H; cbn [hole_value]; lia.
Qed.

Lemma source_count_one t h :
  get_num_undef_trans t = 1 -> t h = None ->
  forall k, k <> h -> t k <> None.
Proof.
  intros Hcount Hh k Hne Hk.
  rewrite source_count_formula in Hcount.
  destruct h as [q s], k as [q' s']; destruct q,s,q',s';
    try (exfalso; apply Hne; reflexivity);
    rewrite Hh,Hk in Hcount; cbn [hole_value] in Hcount; lia.
Qed.

Definition source_support (t : TM) (cut : nat) : Prop :=
  forall q s w d q', t (q,s) = Some (w,d,q') ->
    state_index q < cut /\ state_index q' < cut.

Definition source_good (x : T) : Prop :=
  2 <= min_unused_state x <= 6 /\
  tm x (A,S0) = Some (S1,R,B) /\
  num_undef_trans x = get_num_undef_trans (tm x) /\
  source_support (tm x) (min_unused_state x).

Lemma source_root_good : source_good node0.
Proof.
  unfold source_good, source_support.
  split; [cbn [node0 min_unused_state]; lia|].
  split; [reflexivity|].
  split; [reflexivity|].
  intros q s w d q' H.
  destruct q,s; cbn [node0 tm TM_from_str] in H;
    try discriminate; inversion H; subst; cbn [state_index node0 min_unused_state]; lia.
Qed.

Lemma source_good_child (x : T) h w d q cut' :
  source_good x -> tm x h = None ->
  min_unused_state x <= cut' -> cut' <= 6 ->
  state_index (fst h) < cut' -> state_index q < cut' ->
  source_good (Build_T (tm_upd (tm x) h (w,d,q))
    (Nat.pred (num_undef_trans x)) cut').
Proof.
  intros [Hcut [Hroot [Hcount Hsup]]] Hhole Hle Hmax Hsrc Hdst.
  unfold source_good. cbn [min_unused_state tm num_undef_trans].
  split; [lia|].
  split.
  - rewrite source_upd_miss; [exact Hroot|].
    intro E. subst h. rewrite Hroot in Hhole. discriminate.
  - split.
    + rewrite Hcount. pose proof (source_count_update (tm x) h (w,d,q) Hhole). lia.
    + unfold source_support. intros q0 s0 w0 d0 q1 H.
      destruct (BusyCoq.Eqb.eqb_spec (q0,s0) h) as [E|E].
      * subst h. rewrite source_upd_hit in H. inversion H; subst. cbn in Hsrc. auto.
      * rewrite source_upd_miss in H by exact E.
        destruct (Hsup _ _ _ _ _ H); lia.
Qed.

Theorem source_expand_good x h :
  source_good x -> tm x h = None ->
  state_index (fst h) < min_unused_state x ->
  Forall source_good (expand x h).
Proof.
  destruct x as [t n cut]; cbn [tm min_unused_state].
  intros Hg Hhole Hslot. pose proof Hg as [[Hmin Hmax] _].
  cbn [min_unused_state] in Hmin,Hmax.
  cbn [expand].
  apply Forall_app. split.
  - apply Forall_forall. intros y Hy.
    apply in_flat_map in Hy. destruct Hy as [q [Hq Hy]].
    apply in_flat_map in Hy. destruct Hy as [w [_ Hy]].
    apply in_map_iff in Hy. destruct Hy as [d [<- _]].
    apply state_in_prefix in Hq.
    eapply source_good_child; cbn [tm min_unused_state]; eauto; lia.
  - destruct (skipn cut all_qs) as [|q qs] eqn:E.
    + constructor.
    + apply Forall_forall. intros y Hy.
      apply in_flat_map in Hy. destruct Hy as [w [_ Hy]].
      apply in_map_iff in Hy. destruct Hy as [d [<- _]].
      destruct (fresh_state_index cut q qs E).
      eapply source_good_child; cbn [tm min_unused_state]; eauto; lia.
Qed.

Lemma source_expand'_good x h :
  source_good x -> tm x h = None ->
  state_index (fst h) < min_unused_state x ->
  Forall source_good (expand' x h).
Proof.
  intros Hg Hhole Hslot. unfold expand'.
  destruct (BusyCoq.Eqb.eqb_spec (num_undef_trans x) 1).
  - constructor.
  - eapply source_expand_good; eauto.
Qed.

Lemma source_expand_old_member x h w d q :
  state_index q < min_unused_state x ->
  In (Build_T (tm_upd (tm x) h (w,d,q))
    (Nat.pred (num_undef_trans x)) (min_unused_state x)) (expand x h).
Proof.
  destruct x as [t n cut]; cbn [tm num_undef_trans min_unused_state expand].
  intro H. apply in_or_app. left. apply in_flat_map.
  exists q. split; [apply state_in_prefix; exact H|].
  apply in_flat_map. exists w. split; [apply all_syms_spec|].
  apply in_map. destruct d; simpl; auto.
Qed.

Lemma source_expand_fresh_member x h w d q qs :
  skipn (min_unused_state x) all_qs = q::qs ->
  In (Build_T (tm_upd (tm x) h (w,d,q))
    (Nat.pred (num_undef_trans x)) (S (min_unused_state x))) (expand x h).
Proof.
  destruct x as [t n cut]; cbn [tm num_undef_trans min_unused_state expand].
  intro E. apply in_or_app. right. rewrite E.
  apply in_flat_map. exists w. split; [apply all_syms_spec|].
  apply in_map. destruct d; simpl; auto.
Qed.

Lemma source_expand'_nonlast x h :
  num_undef_trans x <> 1 -> expand' x h = expand x h.
Proof.
  intro H. unfold expand'.
  destruct (BusyCoq.Eqb.eqb_spec (num_undef_trans x) 1); congruence.
Qed.

Print Assumptions source_root_good.
Print Assumptions source_expand'_good.
Print Assumptions source_count_one.
Print Assumptions source_expand_old_member.
Print Assumptions source_expand_fresh_member.
