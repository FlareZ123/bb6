From BusyCoq Require Import Enumerate62 Individual62 SourceResidualRoster.
From Coq Require Import List Arith Lists.Streams Strings.String.

Definition solid26_tm : TM :=
  makeTM (Some (S1,R,B)) (Some (S1,R,D))
    (Some (S1,R,C)) (Some (S0,R,E))
    (Some (S0,L,A)) (Some (S0,R,F))
    (Some (S1,L,A)) (Some (S1,L,D))
    (Some (S1,L,E)) (Some (S0,L,A))
    None (Some (S1,L,A)).

Definition solid26_zero : side := const S0.
Fixpoint solid26_triples (n : nat) (r : side) : side :=
  match n with
  | O => r
  | S k => Cons S1 (Cons S1 (Cons S1 (solid26_triples k r)))
  end.

Lemma solid26_push n r :
  solid26_triples n (Cons S1 r) = Cons S1 (solid26_triples n r).
Proof. induction n; cbn [solid26_triples]; [reflexivity|now rewrite IHn]. Qed.

Definition solid26_family n : Q * tape :=
  (D,(solid26_zero,S1,Cons S1 (Cons S1 (solid26_triples n solid26_zero)))).

Ltac solid26_step :=
  eapply evstep_step;
    [first [eapply step_left; reflexivity | eapply step_right; reflexivity]
    |cbn [move_left move_right hd tl]].

Lemma solid26_prelude n :
  progress solid26_tm (solid26_family n)
    (B,(Cons S1 solid26_zero,S1,Cons S1 (Cons S1 (Cons S1 (solid26_triples n solid26_zero))))).
Proof.
  unfold solid26_family.
  eapply progress_intro; [eapply step_left; reflexivity|].
  cbn [move_left hd tl].
  do 2 solid26_step.
  apply evstep_refl'.
  unfold solid26_zero.
  repeat rewrite <- const_unfold.
  reflexivity.
Qed.

Lemma solid26_rightBlock l r :
  evstep solid26_tm
    (B,(l,S1,Cons S1 (Cons S1 (Cons S1 r))))
    (B,(Cons S1 (Cons S1 (Cons S1 l)),S1,r)).
Proof. do 7 solid26_step. apply evstep_refl'. reflexivity. Qed.

Lemma solid26_rightSweep n l r :
  evstep solid26_tm
    (B,(l,S1,solid26_triples n r))
    (B,(solid26_triples n l,S1,r)).
Proof.
  revert l; induction n as [|n IH]; intro l.
  - cbn [solid26_triples]. constructor.
  - cbn [solid26_triples].
    eapply evstep_trans.
    + apply solid26_rightBlock.
    + specialize (IH (Cons S1 (Cons S1 (Cons S1 l)))).
      repeat rewrite solid26_push in IH. exact IH.
Qed.

Lemma solid26_turn l :
  evstep solid26_tm
    (B,(Cons S1 (Cons S1 l),S1,solid26_zero))
    (D,(Cons S1 l,S1,Cons S1 (Cons S1 solid26_zero))).
Proof.
  do 7 solid26_step. apply evstep_refl'.
  unfold solid26_zero.
  repeat rewrite <- const_unfold. reflexivity.
Qed.

Lemma solid26_leftSweep n l r :
  evstep solid26_tm (D,(solid26_triples n l,S1,r))
    (D,(l,S1,solid26_triples n r)).
Proof.
  revert r; induction n as [|n IH]; intro r.
  - cbn [solid26_triples]. constructor.
  - cbn [solid26_triples].
    do 3 solid26_step.
    specialize (IH (Cons S1 (Cons S1 (Cons S1 r)))).
    repeat rewrite solid26_push in IH. exact IH.
Qed.

Lemma solid26_grow n :
  progress solid26_tm (solid26_family n) (solid26_family (S n)).
Proof.
  eapply progress_evstep_trans; [apply solid26_prelude|].
  eapply evstep_trans;
    [apply (solid26_rightSweep (S n) (Cons S1 solid26_zero) solid26_zero)|].
  eapply evstep_trans;
    [apply (solid26_turn (Cons S1 (solid26_triples n (Cons S1 solid26_zero))) )|].
  rewrite solid26_push.
  unfold solid26_family.
  rewrite <- !solid26_push.
  apply (solid26_leftSweep (S n) solid26_zero (Cons S1 (Cons S1 solid26_zero))).
Qed.

Lemma solid26_start : multistep solid26_tm 8 c0 (solid26_family O).
Proof.
  unfold solid26_family. cbn [solid26_triples].
  do 8 (eapply multistep_S;
    [first [eapply step_left; reflexivity | eapply step_right; reflexivity]
    |cbn [move_left move_right hd tl]]).
  constructor.
Qed.

Theorem solid26_nonhalt : ~ halts solid26_tm c0.
Proof.
  eapply skip_halts; [apply solid26_start|].
  apply progress_nonhalt_simple with (C:=solid26_family) (i0:=O).
  intro n; exists (S n); apply solid26_grow.
Qed.

Open Scope string_scope.
Lemma solid26_table :
  solid26_tm = TM_from_str "1RB1RD_1RC0RE_0LA0RF_1LA1LD_1LE0LA_---1LA".
Proof. reflexivity. Qed.

Theorem solid26_safe bound : source_table_safe bound solid26_tm.
Proof. apply source_nonhalt_cylinder, solid26_nonhalt. Qed.

Print Assumptions solid26_nonhalt.
Print Assumptions solid26_safe.
