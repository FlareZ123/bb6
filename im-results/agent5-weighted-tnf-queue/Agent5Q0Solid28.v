From BusyCoq Require Import Enumerate62 Individual62 SourceResidualRoster.
From Coq Require Import List Arith Lists.Streams Strings.String.

Definition solid28_tm : TM :=
  makeTM (Some (S1,R,B)) (Some (S1,R,D))
    (Some (S1,R,C)) (Some (S0,R,E))
    (Some (S0,L,A)) (Some (S1,R,F))
    (Some (S1,L,A)) (Some (S1,L,D))
    (Some (S1,L,E)) (Some (S0,L,A))
    None (Some (S0,R,E)).

Definition solid28_zero : side := const S0.
Fixpoint solid28_triples (n : nat) (r : side) : side :=
  match n with
  | O => r
  | S k => Cons S1 (Cons S1 (Cons S1 (solid28_triples k r)))
  end.

Lemma solid28_push n r :
  solid28_triples n (Cons S1 r) = Cons S1 (solid28_triples n r).
Proof. induction n; cbn [solid28_triples]; [reflexivity|now rewrite IHn]. Qed.

Definition solid28_family n : Q * tape :=
  (D,(solid28_zero,S1,Cons S1 (Cons S1 (solid28_triples n solid28_zero)))).

Ltac solid28_step :=
  eapply evstep_step;
    [first [eapply step_left; reflexivity | eapply step_right; reflexivity]
    |cbn [move_left move_right hd tl]].

Lemma solid28_prelude n :
  progress solid28_tm (solid28_family n)
    (B,(Cons S1 solid28_zero,S1,Cons S1 (Cons S1 (Cons S1 (solid28_triples n solid28_zero))))).
Proof.
  unfold solid28_family.
  eapply progress_intro; [eapply step_left; reflexivity|].
  cbn [move_left hd tl].
  do 2 solid28_step.
  apply evstep_refl'.
  unfold solid28_zero.
  repeat rewrite <- const_unfold.
  reflexivity.
Qed.

Lemma solid28_first l r :
  evstep solid28_tm (B,(l,S1,Cons S1 (Cons S1 (Cons S1 r))))
    (E,(Cons S0 (Cons S1 (Cons S1 (Cons S1 l))),hd r,tl r)).
Proof. do 6 solid28_step. apply evstep_refl'. reflexivity. Qed.

Lemma solid28_eblock l r :
  evstep solid28_tm (E,(Cons S0 l,S1,Cons S1 (Cons S1 r)))
    (E,(Cons S0 (Cons S1 (Cons S1 (Cons S1 l))),hd r,tl r)).
Proof. do 5 solid28_step. apply evstep_refl'. reflexivity. Qed.

Lemma solid28_esweep n l :
  evstep solid28_tm
    (E,(Cons S0 l,hd (solid28_triples n solid28_zero),tl (solid28_triples n solid28_zero)))
    (E,(Cons S0 (solid28_triples n l),S0,solid28_zero)).
Proof.
  revert l; induction n as [|n IH]; intro l.
  - cbn [solid28_triples solid28_zero hd tl]. constructor.
  - cbn [solid28_triples hd tl].
    eapply evstep_trans.
    + apply solid28_eblock.
    + specialize (IH (Cons S1 (Cons S1 (Cons S1 l)))).
      repeat rewrite solid28_push in IH. exact IH.
Qed.

Lemma solid28_turn l :
  evstep solid28_tm
    (E,(Cons S0 (Cons S1 (Cons S1 l)),S0,solid28_zero))
    (D,(Cons S1 l,S1,Cons S1 (Cons S1 solid28_zero))).
Proof.
  do 6 solid28_step. apply evstep_refl'.
  unfold solid28_zero.
  repeat rewrite <- const_unfold. reflexivity.
Qed.

Lemma solid28_left n l r :
  evstep solid28_tm (D,(solid28_triples n l,S1,r))
    (D,(l,S1,solid28_triples n r)).
Proof.
  revert r; induction n as [|n IH]; intro r.
  - cbn [solid28_triples]. constructor.
  - cbn [solid28_triples].
    do 3 solid28_step.
    specialize (IH (Cons S1 (Cons S1 (Cons S1 r)))).
    repeat rewrite solid28_push in IH. exact IH.
Qed.

Lemma solid28_grow n :
  progress solid28_tm (solid28_family n) (solid28_family (S n)).
Proof.
  eapply progress_evstep_trans; [apply solid28_prelude|].
  eapply evstep_trans; [apply solid28_first|].
  eapply evstep_trans; [apply solid28_esweep|].
  repeat rewrite solid28_push.
  eapply evstep_trans; [apply solid28_turn|].
  unfold solid28_family.
  rewrite <- !solid28_push.
  apply (solid28_left (S n) solid28_zero (Cons S1 (Cons S1 solid28_zero))).
Qed.

Lemma solid28_start : multistep solid28_tm 8 c0 (solid28_family O).
Proof.
  unfold solid28_family. cbn [solid28_triples].
  do 8 (eapply multistep_S;
    [first [eapply step_left; reflexivity | eapply step_right; reflexivity]
    |cbn [move_left move_right hd tl]]).
  constructor.
Qed.

Theorem solid28_nonhalt : ~ halts solid28_tm c0.
Proof.
  eapply skip_halts; [apply solid28_start|].
  apply progress_nonhalt_simple with (C:=solid28_family) (i0:=O).
  intro n; exists (S n); apply solid28_grow.
Qed.

Open Scope string_scope.
Lemma solid28_table :
  solid28_tm = TM_from_str "1RB1RD_1RC0RE_0LA1RF_1LA1LD_1LE0LA_---0RE".
Proof. reflexivity. Qed.

Theorem solid28_safe bound : source_table_safe bound solid28_tm.
Proof. apply source_nonhalt_cylinder, solid28_nonhalt. Qed.

Print Assumptions solid28_nonhalt.
Print Assumptions solid28_safe.
