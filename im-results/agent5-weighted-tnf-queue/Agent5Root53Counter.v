From BusyCoq Require Import Enumerate62 Individual62 SourceResidualRoster.
From Coq Require Import List Arith Lia Lists.Streams Strings.String.
Import ListNotations.
Open Scope nat_scope.

(* Source-native port of Root53.lean.  The formal Lean counterpart proves
   every macro and the full grammar closure; this port requires Rocq CI. *)
Definition r53_tm : TM :=
  makeTM (Some (S1,R,B)) (Some (S1,R,D))
    (Some (S1,R,C)) (Some (S1,R,E))
    (Some (S0,L,A)) (Some (S0,R,C))
    (Some (S1,L,A)) (Some (S1,L,D))
    None (Some (S1,L,F))
    (Some (S1,L,C)) (Some (S0,L,E)).
Local Notation "b ::> s" := (Cons b s) (at level 60, right associativity).
Definition r53_z : side := const S0.
Definition r53_cfg (q:Q) (l:side) (b:Sym) (r:side) : Q*tape := (q,(l,b,r)).
Fixpoint r53_pre (w:list Sym) (s:side) : side :=
  match w with [] => s | b::w' => b ::> r53_pre w' s end.
Fixpoint r53_ones n (s:side) : side :=
  match n with O => s | S k => S1 ::> r53_ones k s end.
Fixpoint r53_zeros n (s:side) : side :=
  match n with O => s | S k => S0 ::> r53_zeros k s end.
Fixpoint r53_alt n (s:side) : side :=
  match n with O => s | S k => S0 ::> S1 ::> r53_alt k s end.
Fixpoint r53_alt10 n (s:side) : side :=
  match n with O => s | S k => S1 ::> S0 ::> r53_alt10 k s end.

Lemma r53_zero_push : S0 ::> r53_z = r53_z.
Proof. unfold r53_z. symmetry. apply const_unfold. Qed.
Lemma r53_ones_add a b s :
  r53_ones (a+b) s = r53_ones a (r53_ones b s).
Proof. induction a; cbn [r53_ones]; [reflexivity|now rewrite IHa]. Qed.
Lemma r53_zeros_add a b s :
  r53_zeros (a+b) s = r53_zeros a (r53_zeros b s).
Proof. induction a; cbn [r53_zeros]; [reflexivity|now rewrite IHa]. Qed.
Lemma r53_ones_push n s :
  r53_ones n (S1 ::> s) = r53_ones (S n) s.
Proof. induction n; cbn [r53_ones]; [reflexivity|now rewrite IHn]. Qed.
Lemma r53_zeros_push n s :
  r53_zeros n (S0 ::> s) = r53_zeros (S n) s.
Proof. induction n; cbn [r53_zeros]; [reflexivity|now rewrite IHn]. Qed.
Lemma r53_alt10_push n s :
  r53_alt10 n (S1 ::> S0 ::> s) = r53_alt10 (S n) s.
Proof. induction n; cbn [r53_alt10]; [reflexivity|now rewrite IHn]. Qed.
Lemma r53_alt10_shift n s :
  r53_alt10 n (S1 ::> s) = S1 ::> r53_alt n s.
Proof. induction n; cbn [r53_alt10 r53_alt]; [reflexivity|now rewrite IHn]. Qed.

Ltac r53_step :=
  eapply evstep_step;
    [first [eapply step_left; reflexivity | eapply step_right; reflexivity]
    |cbn [move_left move_right hd tl]].
Ltac r53_finish_steps :=
  apply evstep_refl'; repeat rewrite r53_zero_push; reflexivity.

Lemma r53_fpair l r :
  evstep r53_tm (r53_cfg F (S1 ::> S1 ::> l) S1 r)
    (r53_cfg F l S1 (S1 ::> S0 ::> r)).
Proof. unfold r53_cfg. do 2 r53_step. r53_finish_steps. Qed.
Lemma r53_flast p r :
  evstep r53_tm (r53_cfg F (S1 ::> S0 ::> p) S1 r)
    (r53_cfg C (tl p) (hd p) (S1 ::> S1 ::> S0 ::> r)).
Proof. unfold r53_cfg. do 3 r53_step. r53_finish_steps. Qed.
Lemma r53_fsweep n p r :
  evstep r53_tm (r53_cfg F (r53_ones (2*n+1) (S0 ::> p)) S1 r)
    (r53_cfg C (tl p) (hd p) (S1 ::> r53_alt10 (S n) r)).
Proof.
  revert r; induction n as [|n IH]; intro r.
  - apply r53_flast.
  - replace (2*S n+1) with (2+(2*n+1)) by lia.
    rewrite r53_ones_add.
    eapply evstep_trans; [apply r53_fpair|].
    specialize (IH (S1 ::> S0 ::> r)).
    rewrite r53_alt10_push in IH. exact IH.
Qed.
Lemma r53_sweep n p r :
  progress r53_tm
    (r53_cfg B (r53_ones (2*n+1) (S0 ::> p)) S1 (S1 ::> r))
    (r53_cfg C (tl p) (hd p) (S1 ::> S1 ::> r53_alt (S n) r)).
Proof.
  unfold r53_cfg.
  eapply progress_intro; [eapply step_right; reflexivity|].
  cbn [move_right hd tl].
  r53_step.
  pose proof (r53_fsweep n p (S1 ::> r)) as H.
  rewrite r53_alt10_shift in H. exact H.
Qed.

Lemma r53_cRun k l r :
  evstep r53_tm
    (r53_cfg C l S1 (r53_ones k (S0 ::> r)))
    (r53_cfg C (S1 ::> S1 ::> r53_zeros k l) (hd r) (tl r)).
Proof.
  revert l; induction k as [|k IH]; intro l.
  - cbn [r53_ones r53_zeros]. unfold r53_cfg.
    do 4 r53_step. r53_finish_steps.
  - cbn [r53_ones]. unfold r53_cfg at 1.
    r53_step.
    specialize (IH (S0 ::> l)).
    rewrite r53_zeros_push in IH. exact IH.
Qed.
Lemma r53_finish n l :
  evstep r53_tm (r53_cfg C l S1 (r53_alt n (S1 ::> S1 ::> r53_z)))
    (r53_cfg B (r53_ones (2*n+1) l) S1 (S1 ::> S1 ::> S1 ::> r53_z)).
Proof.
  revert l; induction n as [|n IH]; intro l.
  - pose proof (r53_cRun 2 l r53_z) as H.
    change (evstep r53_tm
      (r53_cfg C l S1 (S1 ::> S1 ::> S0 ::> r53_z))
      (r53_cfg C (S1 ::> S1 ::> S0 ::> S0 ::> l) S0 r53_z)) in H.
    rewrite r53_zero_push in H.
    eapply evstep_trans; [exact H|].
    unfold r53_cfg; cbn [r53_ones].
    do 9 r53_step. r53_finish_steps.
  - eapply evstep_trans with
      (c':=r53_cfg C (S1 ::> S1 ::> l) S1 (r53_alt n (S1 ::> S1 ::> r53_z))).
    + exact (r53_cRun O l (S1 ::> r53_alt n (S1 ::> S1 ::> r53_z))).
    + replace (2*S n+1) with ((2*n+1)+2) by lia.
      rewrite r53_ones_add. exact (IH (S1 ::> S1 ::> l)).
Qed.

Definition r53_main (p:side) n :=
  r53_cfg B (r53_ones (2*n+1) p) S1 (S1 ::> S1 ::> S1 ::> r53_z).
Lemma r53_ordinary10 u n :
  progress r53_tm (r53_main (S0 ::> S1 ::> u) n)
    (r53_main (S0 ::> S0 ::> u) (S n)).
Proof.
  unfold r53_main.
  eapply progress_evstep_trans; [apply r53_sweep|].
  eapply evstep_trans; [exact (r53_cRun 2 u (S1 ::> r53_alt n (S1 ::> S1 ::> r53_z)))|].
  replace (2*S n+1) with ((2*n+1)+2) by lia.
  rewrite r53_ones_add.
  exact (r53_finish n (S1 ::> S1 ::> S0 ::> S0 ::> u)).
Qed.
Lemma r53_ordinary000 u n :
  progress r53_tm (r53_main (S0 ::> S0 ::> S0 ::> u) n)
    (r53_main (S0 ::> S1 ::> S1 ::> u) (S n)).
Proof.
  unfold r53_main.
  eapply progress_evstep_trans; [apply r53_sweep|].
  cbn [hd tl r53_alt r53_cfg].
  do 3 r53_step.
  eapply evstep_trans; [exact (r53_cRun 1 (S1 ::> S1 ::> u) (S1 ::> r53_alt n (S1 ::> S1 ::> r53_z)))|].
  replace (2*S n+1) with ((2*n+1)+2) by lia.
  rewrite r53_ones_add.
  exact (r53_finish n (S1 ::> S1 ::> S0 ::> S1 ::> S1 ::> u)).
Qed.

Inductive r53_safe_tail : list Sym -> Prop :=
| r53_st_nil : r53_safe_tail []
| r53_st_one xs : r53_safe_tail xs -> r53_safe_tail (S1::xs)
| r53_st_zero_one xs : r53_safe_tail xs -> r53_safe_tail (S0::S1::xs).
Lemma r53_dSweep xs (Hs:r53_safe_tail xs) u r :
  evstep r53_tm
    (r53_cfg D (r53_pre xs (S0 ::> S0 ::> u)) S1 r)
    (r53_cfg B (S1 ::> u) S1 (r53_ones (length xs+1) r)).
Proof.
  revert r; induction Hs as [|xs Hs IH|xs Hs IH]; intro r.
  - cbn [r53_pre length r53_ones]. unfold r53_cfg.
    do 3 r53_step. r53_finish_steps.
  - cbn [r53_pre length]. unfold r53_cfg at 1.
    r53_step.
    specialize (IH (S1 ::> r)).
    rewrite r53_ones_push in IH. exact IH.
  - cbn [r53_pre length]. unfold r53_cfg at 1.
    do 4 r53_step.
    specialize (IH (S1 ::> S1 ::> r)).
    repeat rewrite r53_ones_push in IH. exact IH.
Qed.
Lemma r53_carryFirst xs (Hs:r53_safe_tail xs) u n :
  progress r53_tm
    (r53_main (S0 ::> S0 ::> S1 ::> r53_pre xs (S0 ::> S0 ::> u)) n)
    (r53_cfg B (S1 ::> u) S1 (r53_ones (length xs+4) (r53_alt (S n) (S1 ::> S1 ::> r53_z)))).
Proof.
  unfold r53_main.
  eapply progress_evstep_trans; [apply r53_sweep|].
  cbn [r53_cfg hd tl].
  do 5 r53_step.
  replace (length xs+4) with ((length xs+1)+3) by lia.
  rewrite r53_ones_add.
  exact (r53_dSweep xs Hs u (S1 ::> S1 ::> S1 ::> r53_alt (S n) (S1 ::> S1 ::> r53_z))).
Qed.
Lemma r53_carryFinish k n g :
  evstep r53_tm
    (r53_cfg C (S1 ::> S1 ::> g) S1 (r53_ones k (r53_alt (S n) (S1 ::> S1 ::> r53_z))))
    (r53_main (r53_zeros k (S1 ::> S1 ::> g)) (S n)).
Proof.
  eapply evstep_trans; [exact (r53_cRun k (S1 ::> S1 ::> g) (S1 ::> r53_alt n (S1 ::> S1 ::> r53_z)))|].
  unfold r53_main.
  replace (2*S n+1) with ((2*n+1)+2) by lia.
  rewrite r53_ones_add. apply r53_finish.
Qed.
Lemma r53_carry000 k n u :
  evstep r53_tm
    (r53_cfg B (S1 ::> S0 ::> S0 ::> S0 ::> u) S1
      (r53_ones (S k) (r53_alt (S n) (S1 ::> S1 ::> r53_z))))
    (r53_main (r53_zeros k (S1 ::> S1 ::> S0 ::> S1 ::> S1 ::> u)) (S n)).
Proof.
  eapply evstep_trans; [apply progress_evstep, (r53_sweep O (S0 ::> S0 ::> u) (r53_ones k (r53_alt (S n) (S1 ::> S1 ::> r53_z))))|].
  cbn [r53_cfg hd tl r53_alt].
  do 3 r53_step.
  eapply evstep_trans; [exact (r53_cRun 1 (S1 ::> S1 ::> u)
    (S1 ::> r53_ones k (r53_alt (S n) (S1 ::> S1 ::> r53_z))))|].
  apply r53_carryFinish.
Qed.

Definition r53_block (b d:Sym) := [S0;d;d;b;b].
Inductive r53_core : Sym -> side -> Prop :=
| r53_header : r53_core S1 (S0 ::> S1 ::> S1 ::> r53_z)
| r53_next b d u : r53_core b u -> r53_core d (r53_pre (r53_block b d) u).
Definition r53_phase2 (b:Sym) u := S0 ::> S0 ::> S1 ::> b ::> b ::> u.
Inductive r53_valid : side -> Prop :=
| r53_empty : r53_valid r53_z
| r53_valid_core b u : r53_core b u -> r53_valid u
| r53_carry_header : r53_valid (S0 ::> S0 ::> S1 ::> r53_z)
| r53_valid_carry b u : r53_core b u -> r53_valid (r53_phase2 b u).

Lemma r53_core_false_flip b u (H:r53_core b u) :
  b=S0 -> exists v, u=S0 ::> S0 ::> S0 ::> v /\ r53_core S1 (S0 ::> S1 ::> S1 ::> v).
Proof.
  destruct H as [|b d u H]; intro E; [discriminate|].
  subst d. exists (b ::> b ::> u). split; [reflexivity|].
  exact (r53_next b S1 u H).
Qed.
Fixpoint r53_tailWord k :=
  match k with O => [S0;S1;S1] | S j => S0::S1::S1::S1::S1::r53_tailWord j end.
Lemma r53_tailWord_safe k : r53_safe_tail (r53_tailWord k).
Proof. induction k; cbn [r53_tailWord]; repeat constructor; assumption. Qed.
Lemma r53_tailWord_len k : length (r53_tailWord k)=5*k+3.
Proof. induction k; cbn [r53_tailWord length]; lia. Qed.
Lemma r53_core_true_split b u (H:r53_core b u) :
  b=S1 -> exists k v,
    u=r53_pre (r53_tailWord k) (S0 ::> S0 ::> v) /\
    (v=r53_z \/ r53_core S0 v).
Proof.
  induction H as [|b d u H IH]; intro E.
  - exists O,r53_z. split.
    + cbn [r53_tailWord r53_pre]. repeat rewrite r53_zero_push. reflexivity.
    + left; reflexivity.
  - subst d. destruct b.
    + exists O,u. split; [reflexivity|right; exact H].
    + destruct (IH eq_refl) as [k [v [Hv HC]]].
      exists (S k),v. split; [rewrite Hv; reflexivity|exact HC].
Qed.
Lemma r53_core_zeros k u (H:r53_core S0 u) :
  r53_core S0 (r53_zeros (5*k) u).
Proof.
  induction k as [|k IH].
  - exact H.
  - replace (5*S k) with (5+5*k) by lia.
    rewrite r53_zeros_add. exact (r53_next S0 S0 _ IH).
Qed.

Lemma r53_carry_barrier xs (Hs:r53_safe_tail xs) u n :
  (u=r53_z \/ r53_core S0 u) ->
  exists g, r53_core S1 g /\
    progress r53_tm (r53_main (S0 ::> S0 ::> S1 ::> r53_pre xs (S0 ::> S0 ::> u)) n)
      (r53_main (r53_zeros (length xs+3) (S1 ::> S1 ::> g)) (S n)).
Proof.
  intro Hu. destruct Hu as [Hu|Hu].
  - subst u. exists (S0 ::> S1 ::> S1 ::> r53_z). split; [constructor|].
    eapply progress_evstep_trans; [apply r53_carryFirst; exact Hs|].
    pose proof (r53_carry000 (length xs+3) n r53_z) as H.
    repeat rewrite r53_zero_push in H. exact H.
  - destruct (r53_core_false_flip S0 u Hu eq_refl) as [v [Hv Hg]].
    exists (S0 ::> S1 ::> S1 ::> v). split; [exact Hg|].
    eapply progress_evstep_trans; [apply r53_carryFirst; exact Hs|].
    rewrite Hv. exact (r53_carry000 (length xs+3) n v).
Qed.

Lemma r53_valid_progress p (Hp:r53_valid p) n :
  exists p', r53_valid p' /\ progress r53_tm (r53_main p n) (r53_main p' (S n)).
Proof.
  destruct Hp as [|b p Hc| |b u Hc].
  - exists (S0 ::> S1 ::> S1 ::> r53_z). split.
    + apply r53_valid_core with (b:=S1). constructor.
    + pose proof (r53_ordinary000 r53_z n) as H.
      repeat rewrite r53_zero_push in H. exact H.
  - destruct Hc as [|b d u Hc].
    + exists (S0 ::> S0 ::> S1 ::> r53_z). split.
      * constructor.
      * apply r53_ordinary10.
    + destruct d.
      * exists (r53_pre (r53_block b S1) u). split.
        -- apply r53_valid_core with (b:=S1). apply r53_next. exact Hc.
        -- exact (r53_ordinary000 (b ::> b ::> u) n).
      * exists (r53_phase2 b u). split.
        -- apply r53_valid_carry. exact Hc.
        -- exact (r53_ordinary10 (S1 ::> b ::> b ::> u) n).
  - destruct (r53_carry_barrier [] r53_st_nil r53_z n (or_introl eq_refl)) as [g [Hg H]].
    exists (r53_pre (r53_block S1 S0) g). split.
    + apply r53_valid_core with (b:=S0). apply r53_next. exact Hg.
    + cbn [r53_pre] in H. repeat rewrite r53_zero_push in H. exact H.
  - destruct b.
    + destruct (r53_carry_barrier [] r53_st_nil u n (or_intror Hc)) as [g [Hg H]].
      exists (r53_pre (r53_block S1 S0) g). split.
      * apply r53_valid_core with (b:=S0). apply r53_next. exact Hg.
      * exact H.
    + destruct (r53_core_true_split S1 u Hc eq_refl) as [k [v [Hv HC]]].
      set (xs:=S1::S1::r53_tailWord k).
      assert (Hs:r53_safe_tail xs) by (unfold xs; do 2 constructor; apply r53_tailWord_safe).
      destruct (r53_carry_barrier xs Hs v n HC) as [g [Hg H]].
      assert (E:length xs+3=5*S k+3) by
        (unfold xs; cbn [length]; rewrite r53_tailWord_len; lia).
      rewrite E,r53_zeros_add in H.
      exists (r53_zeros (5*S k) (r53_pre (r53_block S1 S0) g)). split.
      * apply r53_valid_core with (b:=S0). apply r53_core_zeros. apply r53_next. exact Hg.
      * unfold r53_phase2. rewrite Hv. exact H.
Qed.

Lemma r53_start : multistep r53_tm 11 c0 (r53_main r53_z O).
Proof.
  unfold r53_main,r53_cfg,c0,tape0,r53_z. cbn [r53_ones].
  do 11 (eapply multistep_S;
    [first [eapply step_left; reflexivity | eapply step_right; reflexivity]
    |cbn [move_left move_right hd tl]]).
  replace (S1 ::> const S0) with (S1 ::> const S0) by reflexivity.
  constructor.
Qed.
Theorem r53_nonhalt : ~ halts r53_tm c0.
Proof.
  eapply skip_halts; [apply r53_start|].
  apply progress_nonhalt with
    (P:=fun c => exists p n, r53_valid p /\ c=r53_main p n).
  - intros c [p [n [Hp E]]]. subst c.
    destruct (r53_valid_progress p Hp n) as [p' [Hp' Hrun]].
    exists (r53_main p' (S n)). split.
    + exists p',(S n). split; [exact Hp'|reflexivity].
    + exact Hrun.
  - exists r53_z,O. split; [constructor|reflexivity].
Qed.
Open Scope string_scope.
Lemma r53_table : r53_tm = TM_from_str "1RB1RD_1RC1RE_0LA0RC_1LA1LD_---1LF_1LC0LE".
Proof. reflexivity. Qed.
Theorem r53_safe bound : source_table_safe bound r53_tm.
Proof. apply source_nonhalt_cylinder,r53_nonhalt. Qed.
Print Assumptions r53_nonhalt.
Print Assumptions r53_safe.
