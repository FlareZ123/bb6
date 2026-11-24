From BusyCoq Require Import Enumerate62 Individual62.
From Coq Require Import List Arith Lists.Streams.

(* true = E1 1RB; false = E1 0RC. Three rows are undefined. *)
Definition sweep_tm (v : bool) : TM :=
  makeTM (Some (S1,R,B)) (Some (S1,R,D))
    (Some (S1,R,C)) (Some (S1,L,B))
    (Some (S0,L,A)) (Some (S0,L,E))
    (Some (S1,L,A)) (Some (S0,L,B))
    None (Some (if v then (S1,R,B) else (S0,R,C)))
    None None.

Definition sweep_zero : side := const S0.
Fixpoint sweep_ones (n : nat) (r : side) : side :=
  match n with O => r | S n' => Cons S1 (sweep_ones n' r) end.

Lemma sweep_ones_push n r :
  sweep_ones n (Cons S1 r) = Cons S1 (sweep_ones n r).
Proof. induction n; cbn [sweep_ones]; [reflexivity|now rewrite IHn]. Qed.

Definition sweep_end n : Q * tape :=
  (C,(sweep_ones (S n) sweep_zero,S0,sweep_zero)).

Lemma sweep_open v n :
  progress (sweep_tm v) (sweep_end n)
    (B,(sweep_ones n sweep_zero,S1,sweep_zero)).
Proof.
  unfold sweep_end.
  eapply progress_intro; [eapply step_left; reflexivity|].
  cbn [move_left sweep_ones hd tl].
  eapply evstep_step; [eapply step_right; reflexivity|].
  cbn [move_right hd tl].
  eapply evstep_step; [eapply step_left; reflexivity|].
  cbn [move_left hd tl].
  eapply evstep_step; [eapply step_right; reflexivity|].
  cbn [move_right hd tl].
  eapply evstep_step; [eapply step_left; reflexivity|].
  cbn [move_left hd tl].
  apply evstep_refl'.
  unfold sweep_zero.
  repeat rewrite <- const_unfold.
  reflexivity.
Qed.

Lemma sweep_left_run v n r :
  evstep (sweep_tm v) (B,(sweep_ones n sweep_zero,S1,r))
    (B,(sweep_zero,S0,sweep_ones (S n) r)).
Proof.
  revert r; induction n as [|n IH]; intro r.
  - cbn [sweep_ones].
    eapply evstep_step; [eapply step_left; reflexivity|].
    cbn [move_left sweep_zero hd tl].
    constructor.
  - cbn [sweep_ones].
    eapply evstep_step; [eapply step_left; reflexivity|].
    cbn [move_left hd tl].
    specialize (IH (Cons S1 r)).
    rewrite sweep_ones_push in IH.
    exact IH.
Qed.

Lemma sweep_cross v l r :
  evstep (sweep_tm v) (C,(Cons S1 l,S1,r))
    (C,(Cons S1 (Cons S1 l),hd r,tl r)).
Proof.
  destruct v.
  - eapply evstep_step; [eapply step_left; reflexivity|].
    cbn [move_left hd tl].
    eapply evstep_step; [eapply step_right; reflexivity|].
    cbn [move_right hd tl].
    eapply evstep_step; [eapply step_right; reflexivity|].
    cbn [move_right hd tl].
    constructor.
  - eapply evstep_step; [eapply step_left; reflexivity|].
    cbn [move_left hd tl].
    eapply evstep_step; [eapply step_right; reflexivity|].
    cbn [move_right hd tl].
    eapply evstep_step; [eapply step_left; reflexivity|].
    cbn [move_left hd tl].
    eapply evstep_step; [eapply step_right; reflexivity|].
    cbn [move_right hd tl].
    eapply evstep_step; [eapply step_right; reflexivity|].
    cbn [move_right hd tl].
    constructor.
Qed.

Lemma sweep_right_run v n l :
  evstep (sweep_tm v) (C,(Cons S1 l,S1,sweep_ones n sweep_zero))
    (C,(sweep_ones (S (S n)) l,S0,sweep_zero)).
Proof.
  revert l; induction n as [|n IH]; intro l.
  - cbn [sweep_ones].
    exact (sweep_cross v l sweep_zero).
  - eapply evstep_trans with
      (c':=(C,(Cons S1 (Cons S1 l),S1,sweep_ones n sweep_zero))).
    + exact (sweep_cross v l (sweep_ones (S n) sweep_zero)).
    + specialize (IH (Cons S1 l)).
      rewrite sweep_ones_push in IH.
      exact IH.
Qed.

Lemma sweep_grow v n :
  progress (sweep_tm v) (sweep_end n) (sweep_end (S n)).
Proof.
  eapply progress_evstep_trans; [apply sweep_open|].
  eapply evstep_trans; [apply sweep_left_run|].
  eapply evstep_step; [eapply step_right; reflexivity|].
  exact (sweep_right_run v n sweep_zero).
Qed.

Lemma sweep_start v : multistep (sweep_tm v) (S (S O)) c0 (sweep_end (S O)).
Proof.
  eapply multistep_S; [eapply step_right; reflexivity|].
  eapply multistep_S; [eapply step_right; reflexivity|].
  constructor.
Qed.

Theorem sweep_nonhalt v : ~ halts (sweep_tm v) c0.
Proof.
  eapply skip_halts; [apply sweep_start|].
  apply progress_nonhalt_simple with (C:=sweep_end) (i0:=S O).
  intro n; exists (S n); apply sweep_grow.
Qed.

(* These are exactly two active tables from Agent8PackedChunk2_32_32. *)
Open Scope string_scope.
Lemma sweep_true_table :
  sweep_tm true = TM_from_str "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RB_------".
Proof. reflexivity. Qed.
Lemma sweep_false_table :
  sweep_tm false = TM_from_str "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RC_------".
Proof. reflexivity. Qed.

Print Assumptions sweep_nonhalt.
Print Assumptions sweep_true_table.
Print Assumptions sweep_false_table.
