From Coq Require Import List Strings.String Lia.
From BusyCoq Require Import Individual62 Enumerate62 Agent8QueueCheckpoint Agent5PackedChunk12800_20_1000000.
Import ListNotations TNF_Node.
Open Scope string_scope.

(* Exact replay, including an arbitrary untouched tail. No heuristic
   lasso search or finite-run assumption enters the proof. *)
Lemma agent5_replay_lasso (t : TM) (C : Stream Sym -> Q * tape)
    (u : Stream Sym) (F : Stream Sym -> Stream Sym) (n p : nat) :
  multistep_c t n c0 = Some (C u) ->
  (forall v, multistep_c t (S p) (C v) = Some (C (F v))) ->
  ~ halts t c0.
Proof.
  intros H0 H1. eapply multistep_nonhalt.
  - eapply without_counter. apply multistep_c_spec. exact H0.
  - eapply progress_nonhalt_simple with (C := C).
    intro v. exists (F v). apply multistep_progress.
    apply multistep_c_spec. exact (H1 v).
Qed.

Definition short_verdict (x : T) : Prop :=
  (~ halts (tm x) c0) \/
  exists n h, (n <= 13)%nat /\ halts_at (tm x) c0 n h.

Ltac replay_eq := cbn; repeat rewrite <- const_unfold; reflexivity.

Lemma agent5_short_0 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LB1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (B, (v, S1, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S0 v))))
    (n := 4%nat) (p := 7%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_1 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RB1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (A, (v, S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S1 (Cons S0 v)))))
    (n := 0%nat) (p := 12%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_2 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LB1RF",1,6)).
Proof.
  unfold short_verdict. right. exists 13%nat, (D, S1). split; [lia|].
  eapply halts_at_intro with (l := (Cons S0 (Cons S1 (const S0)))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_3 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RB1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (B, ((Cons S1 v), S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S1 (Cons S0 v)))))
    (n := 1%nat) (p := 10%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_4 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LC1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (E, ((Cons S1 v), S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 v)))
    (n := 6%nat) (p := 6%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_5 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RC1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (B, ((Cons S1 v), S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S0 v))))
    (n := 1%nat) (p := 11%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_6 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LC1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (C, (v, S1, (Cons S1 (const S0)))))) (u := (const S0)) (F := (fun v => (Cons S1 v)))
    (n := 7%nat) (p := 4%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_7 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RC1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (C, ((Cons S1 v), S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S1 (Cons S0 v)))))
    (n := 3%nat) (p := 8%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_8 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LD1RF",1,6)).
Proof.
  unfold short_verdict. right. exists 12%nat, (D, S1). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (const S0))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_9 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RD1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (D, (v, S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S0 (Cons S1 (Cons S1 v)))))
    (n := 5%nat) (p := 6%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_10 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LD1RF",1,6)).
Proof.
  unfold short_verdict. right. exists 12%nat, (D, S1). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (const S0))) (r := (Cons S1 (const S0))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_11 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RD1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (D, (v, S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S1 (Cons S1 v)))))
    (n := 5%nat) (p := 6%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_12 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LE1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun _ => (E, ((Cons S1 (const S0)), S1, (const S0))))) (u := (const S0)) (F := (fun v => v))
    (n := 8%nat) (p := 3%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_13 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RE1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (E, ((Cons S1 v), S1, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S0 (Cons S1 v))))
    (n := 8%nat) (p := 7%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_14 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LE1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (F, (v, S1, (Cons S1 (const S0)))))) (u := (const S0)) (F := (fun v => (Cons S1 v)))
    (n := 9%nat) (p := 4%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_15 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RE1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (E, ((Cons S1 v), S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S1 v))))
    (n := 6%nat) (p := 5%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_16 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0LF1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun _ => (F, ((Cons S1 (const S0)), S1, (const S0))))) (u := (const S0)) (F := (fun v => v))
    (n := 10%nat) (p := 1%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_17 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_0RF1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (F, (v, S0, (const S0))))) (u := (Cons S1 (Cons S1 (const S0)))) (F := (fun v => (Cons S0 v)))
    (n := 11%nat) (p := 0%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_18 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1LF1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (F, (v, S1, (Cons S1 (const S0)))))) (u := (const S0)) (F := (fun v => (Cons S1 v)))
    (n := 9%nat) (p := 2%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_19 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1LF_1RF1RF",1,6)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (F, (v, S0, (const S0))))) (u := (Cons S1 (Cons S1 (const S0)))) (F := (fun v => (Cons S1 v)))
    (n := 11%nat) (p := 0%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_20 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RE_1RE---_1LC1RF_------",3,6)).
Proof.
  unfold short_verdict. right. exists 9%nat, (F, S0). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (Cons S1 (const S0)))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_21 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB0LF_1RE---_1LC---_------",4,6)).
Proof.
  unfold short_verdict. right. exists 8%nat, (F, S0). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (Cons S0 (Cons S1 (const S0)))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_22 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB0RF_1RE---_1LC---_------",4,6)).
Proof.
  unfold short_verdict. right. exists 8%nat, (F, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_23 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1LF_1RE---_1LC---_------",4,6)).
Proof.
  unfold short_verdict. right. exists 8%nat, (F, S0). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (Cons S1 (Cons S1 (const S0)))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_24 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB1RF_1RE---_1LC---_------",4,6)).
Proof.
  unfold short_verdict. right. exists 8%nat, (F, S1). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (const S0))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_25 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_1RC---_------",5,5)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (C, ((Cons S1 v), S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S0 v))))
    (n := 3%nat) (p := 3%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_26 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_0LD---_------",5,5)).
Proof.
  unfold short_verdict. right. exists 7%nat, (D, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_27 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_0RD---_------",5,5)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (D, (v, S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S0 (Cons S1 v))))
    (n := 5%nat) (p := 1%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_28 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_1LD---_------",5,5)).
Proof.
  unfold short_verdict. right. exists 7%nat, (D, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (Cons S1 (const S0))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_29 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_1RD---_------",5,5)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (D, (v, S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S1 v))))
    (n := 5%nat) (p := 1%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_30 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_0LE---_------",5,5)).
Proof.
  unfold short_verdict. right. exists 7%nat, (E, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_31 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_0RE---_------",5,5)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (E, (v, S0, (const S0))))) (u := (Cons S1 (const S0))) (F := (fun v => (Cons S0 v)))
    (n := 6%nat) (p := 0%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_32 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_1LE---_------",5,5)).
Proof.
  unfold short_verdict. right. exists 7%nat, (E, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (Cons S1 (const S0))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_33 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_1RE---_------",5,5)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (E, (v, S0, (const S0))))) (u := (Cons S1 (const S0))) (F := (fun v => (Cons S1 v)))
    (n := 6%nat) (p := 0%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_34 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_0LF---_------",5,6)).
Proof.
  unfold short_verdict. right. exists 7%nat, (F, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_35 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_0RF---_------",5,6)).
Proof.
  unfold short_verdict. right. exists 7%nat, (F, S0). split; [lia|].
  eapply halts_at_intro with (l := (Cons S0 (Cons S1 (const S0)))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_36 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_1LF---_------",5,6)).
Proof.
  unfold short_verdict. right. exists 7%nat, (F, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (Cons S1 (const S0))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_37 : short_verdict (decode_node ("1RB1RC_0LA0RD_0LB---_1RE---_1RF---_------",5,6)).
Proof.
  unfold short_verdict. right. exists 7%nat, (F, S0). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (Cons S1 (const S0)))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_38 : short_verdict (decode_node ("1RB1RC_0LA1LD_0LB---_------_------_------",7,4)).
Proof.
  unfold short_verdict. right. exists 5%nat, (D, S0). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (Cons S1 (const S0))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_39 : short_verdict (decode_node ("1RB1RC_0LA1RD_0LB---_------_------_------",7,4)).
Proof.
  unfold short_verdict. right. exists 5%nat, (D, S0). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (const S0))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_40 : short_verdict (decode_node ("1RB1RC_0LA---_1LA0LA_------_------_------",7,3)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun _ => (A, ((const S0), S1, (const S0))))) (u := (const S0)) (F := (fun v => v))
    (n := 2%nat) (p := 3%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_41 : short_verdict (decode_node ("1RB1RC_0LA---_1LA0RA_------_------_------",7,3)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (A, (v, S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S0 (Cons S1 v))))
    (n := 0%nat) (p := 5%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_42 : short_verdict (decode_node ("1RB1RC_0LA---_1LA1LA_------_------_------",7,3)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun _ => (A, ((const S0), S1, (Cons S1 (const S0)))))) (u := (const S0)) (F := (fun v => v))
    (n := 4%nat) (p := 1%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_43 : short_verdict (decode_node ("1RB1RC_0LA---_1LA1RA_------_------_------",7,3)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (A, (v, S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 (Cons S1 v))))
    (n := 0%nat) (p := 5%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_44 : short_verdict (decode_node ("1RB1RC_0LA---_1LA0LB_------_------_------",7,3)).
Proof.
  unfold short_verdict. right. exists 6%nat, (B, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_45 : short_verdict (decode_node ("1RB1RC_0LA---_1LA0RB_------_------_------",7,3)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (A, (v, S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 v)))
    (n := 0%nat) (p := 6%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_46 : short_verdict (decode_node ("1RB1RC_0LA---_1LA1LB_------_------_------",7,3)).
Proof.
  unfold short_verdict. right. exists 6%nat, (B, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (Cons S1 (const S0))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_47 : short_verdict (decode_node ("1RB1RC_0LA---_1LA1RB_------_------_------",7,3)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (B, ((Cons S1 v), S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 v)))
    (n := 1%nat) (p := 4%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_48 : short_verdict (decode_node ("1RB1RC_0LA---_1LA0LC_------_------_------",7,3)).
Proof.
  unfold short_verdict. right. exists 9%nat, (B, S1). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (const S0))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_49 : short_verdict (decode_node ("1RB1RC_0LA---_1LA0RC_------_------_------",7,3)).
Proof.
  unfold short_verdict. right. exists 8%nat, (B, S1). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (Cons S1 (const S0)))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_50 : short_verdict (decode_node ("1RB1RC_0LA---_1LA1LC_------_------_------",7,3)).
Proof.
  unfold short_verdict. right. exists 9%nat, (B, S1). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (const S0))) (r := (Cons S1 (Cons S1 (const S0)))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_51 : short_verdict (decode_node ("1RB1RC_0LA---_1LA1RC_------_------_------",7,3)).
Proof.
  unfold short_verdict. left. eapply agent5_replay_lasso with
    (C := (fun v => (C, ((Cons S1 v), S0, (const S0))))) (u := (const S0)) (F := (fun v => (Cons S1 v)))
    (n := 3%nat) (p := 2%nat).
  - replay_eq.
  - intro v. replay_eq.
Qed.

Lemma agent5_short_52 : short_verdict (decode_node ("1RB1RC_0LA---_1LA0LD_------_------_------",7,4)).
Proof.
  unfold short_verdict. right. exists 6%nat, (D, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_53 : short_verdict (decode_node ("1RB1RC_0LA---_1LA0RD_------_------_------",7,4)).
Proof.
  unfold short_verdict. right. exists 6%nat, (D, S0). split; [lia|].
  eapply halts_at_intro with (l := (Cons S0 (Cons S1 (const S0)))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_54 : short_verdict (decode_node ("1RB1RC_0LA---_1LA1LD_------_------_------",7,4)).
Proof.
  unfold short_verdict. right. exists 6%nat, (D, S1). split; [lia|].
  eapply halts_at_intro with (l := (const S0)) (r := (Cons S1 (const S0))).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Lemma agent5_short_55 : short_verdict (decode_node ("1RB1RC_0LA---_1LA1RD_------_------_------",7,4)).
Proof.
  unfold short_verdict. right. exists 6%nat, (D, S0). split; [lia|].
  eapply halts_at_intro with (l := (Cons S1 (Cons S1 (const S0)))) (r := (const S0)).
  - apply multistep_c_spec. replay_eq.
  - reflexivity.
Qed.

Theorem agent5_last20_short_verdicts :
  Forall short_verdict (fst (decode_queue packed_chunk_12800_20_1000000)).
Proof.
  cbn [decode_queue fst packed_chunk_12800_20_1000000 map].
  constructor; [exact agent5_short_0|].
  constructor; [exact agent5_short_1|].
  constructor; [exact agent5_short_2|].
  constructor; [exact agent5_short_3|].
  constructor; [exact agent5_short_4|].
  constructor; [exact agent5_short_5|].
  constructor; [exact agent5_short_6|].
  constructor; [exact agent5_short_7|].
  constructor; [exact agent5_short_8|].
  constructor; [exact agent5_short_9|].
  constructor; [exact agent5_short_10|].
  constructor; [exact agent5_short_11|].
  constructor; [exact agent5_short_12|].
  constructor; [exact agent5_short_13|].
  constructor; [exact agent5_short_14|].
  constructor; [exact agent5_short_15|].
  constructor; [exact agent5_short_16|].
  constructor; [exact agent5_short_17|].
  constructor; [exact agent5_short_18|].
  constructor; [exact agent5_short_19|].
  constructor; [exact agent5_short_20|].
  constructor; [exact agent5_short_21|].
  constructor; [exact agent5_short_22|].
  constructor; [exact agent5_short_23|].
  constructor; [exact agent5_short_24|].
  constructor; [exact agent5_short_25|].
  constructor; [exact agent5_short_26|].
  constructor; [exact agent5_short_27|].
  constructor; [exact agent5_short_28|].
  constructor; [exact agent5_short_29|].
  constructor; [exact agent5_short_30|].
  constructor; [exact agent5_short_31|].
  constructor; [exact agent5_short_32|].
  constructor; [exact agent5_short_33|].
  constructor; [exact agent5_short_34|].
  constructor; [exact agent5_short_35|].
  constructor; [exact agent5_short_36|].
  constructor; [exact agent5_short_37|].
  constructor; [exact agent5_short_38|].
  constructor; [exact agent5_short_39|].
  constructor; [exact agent5_short_40|].
  constructor; [exact agent5_short_41|].
  constructor; [exact agent5_short_42|].
  constructor; [exact agent5_short_43|].
  constructor; [exact agent5_short_44|].
  constructor; [exact agent5_short_45|].
  constructor; [exact agent5_short_46|].
  constructor; [exact agent5_short_47|].
  constructor; [exact agent5_short_48|].
  constructor; [exact agent5_short_49|].
  constructor; [exact agent5_short_50|].
  constructor; [exact agent5_short_51|].
  constructor; [exact agent5_short_52|].
  constructor; [exact agent5_short_53|].
  constructor; [exact agent5_short_54|].
  constructor; [exact agent5_short_55|].
  constructor.
Qed.
Print Assumptions agent5_last20_short_verdicts.
