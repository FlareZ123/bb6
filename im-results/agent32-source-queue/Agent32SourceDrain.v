From BusyCoq Require Import Enumerate62 Eqb Agent32Q0Partition.
From Coq Require Import List NArith Lia.
Import ListNotations.
Import TNF_Node.

(* Purely structural: actual source queue termination does not depend on
   soundness of the verdict function. *)
Fixpoint weight (n : nat) : N :=
  match n with O => 1%N | S k => (25 * weight k)%N end.

Fixpoint massCounts (xs : list nat) : N :=
  match xs with [] => 0%N | n::ys => (weight n + massCounts ys)%N end.

Definition mass (xs : list T) : N := massCounts (List.map num_undef_trans xs).
Definition wf (q : SearchQueue) : Prop :=
  Forall (fun x => (0 < num_undef_trans x)%nat) (fst q).

Lemma weight_pos n : (0 < weight n)%N.
Proof. induction n; simpl only [weight]; lia. Qed.

Lemma mass_cons x xs : mass (x::xs) = (weight (num_undef_trans x) + mass xs)%N.
Proof. reflexivity. Qed.

Lemma mass_app xs ys : mass (xs++ys) = (mass xs + mass ys)%N.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  simpl only [app, mass_cons]; rewrite IH; lia.
Qed.

Lemma mass_nonempty xs : xs <> [] -> (0 < mass xs)%N.
Proof.
  destruct xs as [|x xs]; [contradiction|].
  intros _; rewrite mass_cons; pose proof (weight_pos (num_undef_trans x)); lia.
Qed.

Lemma mass_repeat n k : massCounts (repeat n k) = (N.of_nat k * weight n)%N.
Proof.
  induction k; [reflexivity|].
  simpl only [repeat, massCounts].
  rewrite IHk, Nat2N.inj_succ.
  nia.
Qed.

Lemma expand_meta x h :
  (0 < num_undef_trans x)%nat ->
  exists k, (k<=24)%nat /\
    List.map num_undef_trans (expand' x h) = repeat (Nat.pred (num_undef_trans x)) k.
Proof.
  destruct x as [tm [|[|n]] m]; [cbn; lia| |].
  - intros _; exists 0%nat; split; [lia|reflexivity].
  - intros _.
    destruct m as [|[|[|[|[|[|m]]]]]].
    + exists 4%nat; split; [lia|reflexivity].
    + exists 8%nat; split; [lia|reflexivity].
    + exists 12%nat; split; [lia|reflexivity].
    + exists 16%nat; split; [lia|reflexivity].
    + exists 20%nat; split; [lia|reflexivity].
    + exists 24%nat; split; [lia|reflexivity].
    + exists 24%nat; split; [lia|reflexivity].
Qed.

Lemma expand_mass_lt x h :
  (0 < num_undef_trans x)%nat ->
  (mass (expand' x h) < weight (num_undef_trans x))%N.
Proof.
  intros H.
  destruct (expand_meta x h H) as [k [Hk Hmap]].
  unfold mass; rewrite Hmap, mass_repeat.
  destruct (num_undef_trans x) as [|n] eqn:E; [lia|].
  simpl only [Nat.pred,weight].
  pose proof (weight_pos n).
  assert (N.of_nat k <= 24)%N by lia.
  nia.
Qed.

Lemma expand_pos x h :
  (0 < num_undef_trans x)%nat ->
  Forall (fun y => (0 < num_undef_trans y)%nat) (expand' x h).
Proof.
  intros H.
  apply Forall_forall.
  intros y Hy.
  destruct (num_undef_trans x) as [|[|n]] eqn:E; [lia| |].
  - unfold expand' in Hy; rewrite E in Hy; cbn in Hy; contradiction.
  - destruct (expand_meta x h H) as [k [Hk Hmap]].
    pose proof (in_map num_undef_trans _ _ Hy) as Hmem.
    rewrite Hmap,E in Hmem.
    apply repeat_spec in Hmem.
    lia.
Qed.

Lemma update_decreases (f : TM -> DecideResult) q q' :
  wf q ->
  SearchQueue_upd f q = inl q' ->
  wf q' /\ (mass (fst q') < mass (fst q))%N.
Proof.
  destruct q as [[|x xs] ys].
  - intros _ H; discriminate.
  - intros Hw H.
    unfold wf in Hw; cbn [fst] in Hw.
    inversion Hw as [|? ? Hpos Htail]; subst.
    unfold SearchQueue_upd in H.
    destruct (f (tm x)) as [h| |] eqn:E; inversion H; subst q'; clear H.
    + split.
      * unfold wf; cbn [fst]; apply Forall_app; split; [apply expand_pos; exact Hpos|exact Htail].
      * cbn [fst]; rewrite mass_app,mass_cons.
        pose proof (expand_mass_lt x h Hpos); lia.
    + split; [exact Htail|].
      cbn [fst]; rewrite mass_cons.
      pose proof (weight_pos (num_undef_trans x)); lia.
    + split; [exact Htail|].
      cbn [fst]; rewrite mass_cons.
      pose proof (weight_pos (num_undef_trans x)); lia.
Qed.

Lemma update_inr_empty f q q' :
  SearchQueue_upd f q = inr q' -> fst q' = [].
Proof.
  destruct q as [[|x xs] ys]; cbn [SearchQueue_upd].
  - intros H; inversion H; reflexivity.
  - destruct (f (tm x)); discriminate.
Qed.

(* Binary positive iteration, with early exits.  If the result is still inl
   after p iterations then exactly p successful active updates occurred. *)
Lemma pos_iter_decrease (f : TM -> DecideResult) p q q' :
  wf q ->
  Pos_iter_until (SearchQueue_upd f) (inl q) p = inl q' ->
  wf q' /\ (mass (fst q') + N.pos p <= mass (fst q))%N.
Proof.
  revert q q'.
  induction p as [p IH|p IH|]; intros q q' Hw Hrun.
  - cbn [Pos_iter_until] in Hrun.
    destruct (SearchQueue_upd f q) as [q1|q1] eqn:E1; [|destruct p; discriminate].
    destruct (Pos_iter_until (SearchQueue_upd f) (inl q1) p) as [q2|q2] eqn:E2; [|destruct p; discriminate].
    destruct (update_decreases f q q1 Hw E1) as [Hw1 Hm1].
    destruct (IH q1 q2 Hw1 E2) as [Hw2 Hm2].
    destruct (IH q2 q' Hw2 Hrun) as [Hw3 Hm3].
    split; [exact Hw3|lia].
  - cbn [Pos_iter_until] in Hrun.
    destruct (Pos_iter_until (SearchQueue_upd f) (inl q) p) as [q1|q1] eqn:E1; [|destruct p; discriminate].
    destruct (IH q q1 Hw E1) as [Hw1 Hm1].
    destruct (IH q1 q' Hw1 Hrun) as [Hw2 Hm2].
    split; [exact Hw2|lia].
  - cbn [Pos_iter_until] in Hrun.
    destruct (update_decreases f q q' Hw Hrun) as [Hw' Hm].
    split; [exact Hw'|lia].
Qed.

Lemma pos_iter_inr_empty (f : TM -> DecideResult) p q q' :
  Pos_iter_until (SearchQueue_upd f) (inl q) p = inr q' ->
  fst q' = [].
Proof.
  revert q q'.
  induction p as [p IH|p IH|]; intros q q' Hrun.
  - cbn [Pos_iter_until] in Hrun.
    destruct (SearchQueue_upd f q) as [q1|q1] eqn:E1.
    + destruct (Pos_iter_until (SearchQueue_upd f) (inl q1) p) as [q2|q2] eqn:E2.
      * eapply IH; exact Hrun.
      * destruct p; inversion Hrun; subst; eapply IH; eassumption.
    + destruct p; inversion Hrun; subst; eapply update_inr_empty; eassumption.
  - cbn [Pos_iter_until] in Hrun.
    destruct (Pos_iter_until (SearchQueue_upd f) (inl q) p) as [q1|q1] eqn:E1.
    + eapply IH; exact Hrun.
    + destruct p; inversion Hrun; subst; eapply IH; eassumption.
  - cbn [Pos_iter_until] in Hrun.
    eapply update_inr_empty; eassumption.
Qed.

Theorem source_updates_drain f q fuel :
  wf q ->
  (mass (fst q) <= fuel)%N ->
  fst (SearchQueue_upds f q fuel) = [].
Proof.
  intros Hw Hfuel.
  unfold SearchQueue_upds,N_iter_until.
  destruct fuel as [|p].
  - cbn [get_SQ].
    destruct (fst q) as [|x xs] eqn:E; [reflexivity|].
    pose proof (mass_nonempty (fst q) ltac:(rewrite E; discriminate)); lia.
  - destruct (Pos_iter_until (SearchQueue_upd f) (inl q) p) as [q'|q'] eqn:E.
    + cbn [get_SQ].
      destruct (pos_iter_decrease f p q q' Hw E) as [_ Hm].
      destruct (fst q') as [|x xs] eqn:E'; [reflexivity|].
      pose proof (mass_nonempty (fst q') ltac:(rewrite E'; discriminate)); lia.
    + cbn [get_SQ]. eapply pos_iter_inr_empty; exact E.
Qed.

Lemma q0_chunk_uniform l sz :
  Forall (fun x => num_undef_trans x = 7%nat) (fst (q_i l sz)).
Proof.
  apply Forall_forall; intros x Hx.
  apply agent32_q0_uniform.
  unfold q_i in Hx; cbn [fst] in Hx.
  apply in_firstn in Hx.
  apply in_skipn in Hx.
  exact Hx.
Qed.

Lemma uniform_mass xs n :
  Forall (fun x => num_undef_trans x = n) xs ->
  mass xs = (N.of_nat (length xs) * weight n)%N.
Proof.
  intros H; induction H; [reflexivity|].
  rewrite mass_cons,H,IHForall.
  simpl only [length].
  rewrite Nat2N.inj_succ; nia.
Qed.

(* The actual source's 100-node chunks have a much smaller potential than
   the generic root bound. No assumed classifier theorem is needed here. *)
Theorem actual_q0_chunk_drains i :
  (i < 129)%nat ->
  fst (SearchQueue_upds decider (q_i (100*i) 100) MAXT) = [].
Proof.
  intros Hi.
  pose proof (q0_chunk_uniform (100*i) 100) as Hu.
  apply source_updates_drain.
  - unfold wf; eapply Forall_impl; [|exact Hu]; intros x Hx; lia.
  - rewrite (uniform_mass _ 7 Hu), agent32_q0_chunk_length by exact Hi.
    destruct (Nat.eqb i 128); vm_compute; congruence.
Qed.

Print Assumptions source_updates_drain.
Print Assumptions actual_q0_chunk_drains.
