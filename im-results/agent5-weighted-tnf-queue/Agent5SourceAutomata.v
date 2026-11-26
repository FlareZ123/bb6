From BusyCoq Require Import Individual62 Enumerate62 Agent5Enumerate62DeciderSound.
From Coq Require Import List Bool Arith Lia.
Import ListNotations TNF_Node.
Open Scope nat_scope.

(* Direct finite-stack closure; no search or MITM saturation in the proof checker. *)
Record auto_stack : Type := {
  a_pop : list (list (Sym*nat));
  a_push : list (nat*nat)
}.
Definition pop_at (a : auto_stack) (i : nat) := nth i (a_pop a) [].
Definition push_at (a : auto_stack) (i : nat) (s : Sym) :=
  match s with S0 => fst (nth i (a_push a) (0,0))
             | S1 => snd (nth i (a_push a) (0,0)) end.
Definition edge_in (s : Sym) (i : nat) (es : list (Sym*nat)) :=
  existsb (fun e => andb (sym_eqb s (fst e)) (Nat.eqb i (snd e))) es.
Lemma edge_in_sound s i es : edge_in s i es = true -> In (s,i) es.
Proof.
  unfold edge_in. rewrite existsb_exists.
  intros [[s' i'] [Hin H]]. cbn in H.
  apply andb_true_iff in H. destruct H as [Hs Hi].
  destruct (sym_eqb_spec s s'); [|congruence].
  apply Nat.eqb_eq in Hi. subst. exact Hin.
Qed.

Definition auto_row := (Q*Sym*nat*nat)%type.
Definition row_in (a : auto_row) (rows : list auto_row) :=
  let '(q,s,i,j) := a in
  existsb (fun r => let '(q',s',i',j') := r in
    andb (q_eqb q q') (andb (sym_eqb s s') (andb (Nat.eqb i i') (Nat.eqb j j')))) rows.
Lemma row_in_sound a rows : row_in a rows = true -> In a rows.
Proof.
  destruct a as [[[q s] i] j]. unfold row_in. rewrite existsb_exists.
  intros [[[[q' s'] i'] j'] [Hin H]].
  rewrite !andb_true_iff in H. destruct H as [Hq [Hs [Hi Hj]]].
  destruct (q_eqb_spec q q'); [|congruence].
  destruct (sym_eqb_spec s s'); [|congruence].
  apply Nat.eqb_eq in Hi. apply Nat.eqb_eq in Hj. subst. exact Hin.
Qed.

Record auto_cert : Type := {
  a_left : auto_stack;
  a_right : auto_stack;
  a_rows : list auto_row
}.
Definition row_check (p : TM) (c : auto_cert) (r : auto_row) :=
  let '(q,s,i,j) := r in
  match p (q,s) with
  | None => false
  | Some (w,L,q') =>
    let k := push_at (a_right c) j w in
    andb (edge_in w j (pop_at (a_right c) k))
      (forallb (fun e => row_in (q',fst e,snd e,k) (a_rows c)) (pop_at (a_left c) i))
  | Some (w,R,q') =>
    let k := push_at (a_left c) i w in
    andb (edge_in w i (pop_at (a_left c) k))
      (forallb (fun e => row_in (q',fst e,k,snd e) (a_rows c)) (pop_at (a_right c) j))
  end.
Definition auto_cert_check (p : TM) (c : auto_cert) :=
  andb (edge_in S0 0 (pop_at (a_left c) 0))
    (andb (edge_in S0 0 (pop_at (a_right c) 0))
      (andb (row_in (q0,S0,0,0) (a_rows c))
        (forallb (row_check p c) (a_rows c)))).

Inductive stack_accept (a : auto_stack) : list Sym -> nat -> Prop :=
| accept_nil : stack_accept a [] 0
| accept_cons : forall s xs i j,
    stack_accept a xs i -> In (s,i) (pop_at a j) -> stack_accept a (s::xs) j.

Lemma accept_pop a xs i :
  In (S0,0) (pop_at a 0) ->
  stack_accept a xs i ->
  exists j, In (hd S0 xs,j) (pop_at a i) /\ stack_accept a (tl xs) j.
Proof.
  intros Hblank H. destruct H.
  - exists 0. cbn. split; [exact Hblank|constructor].
  - cbn. eauto.
Qed.

Definition auto_inv (c : auto_cert) (x : cconfig) :=
  let '(l,r,s,q) := x in
  exists i j, In (q,s,i,j) (a_rows c) /\
    stack_accept (a_left c) l i /\ stack_accept (a_right c) r j.

Lemma auto_inv_blank p c :
  auto_cert_check p c = true -> auto_inv c agent32_finiteBlank.
Proof.
  unfold auto_cert_check. rewrite !andb_true_iff.
  intros [_ [_ [Hr _]]]. exists 0,0.
  split; [apply row_in_sound; exact Hr|split; constructor].
Qed.

Lemma auto_inv_step p c x :
  auto_cert_check p c = true -> auto_inv c x ->
  exists y, cconfig_step p x = Some y /\ auto_inv c y.
Proof.
  destruct x as [[[l r] s] q].
  unfold auto_cert_check. rewrite !andb_true_iff.
  intros [Hbl [Hbr [_ Hall]]] [i [j [Hin [Hl Hr]]]].
  apply forallb_forall with (x:=(q,s,i,j)) in Hall; [|exact Hin].
  unfold row_check in Hall.
  destruct (p (q,s)) as [[[w d] q']|] eqn:E; [|discriminate].
  destruct d.
  - cbn in Hall. apply andb_true_iff in Hall.
    destruct Hall as [Hpush Hnext].
    destruct (accept_pop _ _ _ (edge_in_sound _ _ _ Hbl) Hl) as [i' [He Hp]].
    apply forallb_forall with (x:=(hd S0 l,i')) in Hnext; [|exact He].
    exists (tl l,w::r,hd S0 l,q'). split.
    + cbn [cconfig_step]. rewrite E. reflexivity.
    + cbn [auto_inv]. exists i', (push_at (a_right c) j w).
      split; [apply row_in_sound; exact Hnext|].
      split; [exact Hp|eapply accept_cons; [exact Hr|apply edge_in_sound; exact Hpush]].
  - cbn in Hall. apply andb_true_iff in Hall.
    destruct Hall as [Hpush Hnext].
    destruct (accept_pop _ _ _ (edge_in_sound _ _ _ Hbr) Hr) as [j' [He Hp]].
    apply forallb_forall with (x:=(hd S0 r,j')) in Hnext; [|exact He].
    exists (w::l,tl r,hd S0 r,q'). split.
    + cbn [cconfig_step]. rewrite E. reflexivity.
    + cbn [auto_inv]. exists (push_at (a_left c) i w),j'.
      split; [apply row_in_sound; exact Hnext|].
      split; [eapply accept_cons; [exact Hl|apply edge_in_sound; exact Hpush]|exact Hp].
Qed.

Lemma auto_inv_run p c n x :
  auto_cert_check p c = true -> auto_inv c x ->
  exists y, agent32_finiteRun p n x = Some y /\ auto_inv c y.
Proof.
  revert x. induction n as [|n IH]; intros x Hc Hx.
  - exists x. split; [reflexivity|exact Hx].
  - destruct (auto_inv_step p c x Hc Hx) as [z [Hz Hinv]].
    destruct (IH z Hc Hinv) as [y [Hy Hsafe]].
    exists y. split; [cbn [agent32_finiteRun]; now rewrite Hz|exact Hsafe].
Qed.

Theorem auto_cert_nonhalt p c :
  auto_cert_check p c = true -> ~ halts p c0.
Proof.
  intro H. apply (proj2 nonhalt_iff). intro n.
  destruct (auto_inv_run p c n agent32_finiteBlank H (auto_inv_blank p c H))
    as [x [Hr _]].
  exists (cconfig_to_config x).
  apply multistep_c_spec.
  pose proof (agent32_cconfig_run_commute p n agent32_finiteBlank) as HC.
  rewrite agent32_finiteBlank_correct, Hr in HC.
  exact HC.
Qed.

Print Assumptions auto_cert_nonhalt.
