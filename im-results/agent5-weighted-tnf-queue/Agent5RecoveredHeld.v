From BusyCoq Require Import CTL62 Agent8GlobalSource SourceResidualRoster Individual62.
From Coq Require Import Strings.String.
Open Scope string_scope.

(* Actual q_i 2800 100 held node, reflected into original FARv3.nonhalt208.
   Recheck just its certificate, not the full upstream theorem family. *)
Definition recovered_held_2800 : TM :=
  TM_from_str "1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---".
Definition recovered_held_2800_reflected : TM :=
  TM_from_str "1LB0LD_1RC1RB_0RE1LA_0RC0LA_1RF1RD_1LD---".

Lemma recovered_held_2800_far :
  ~ halts (TM_from_str "1LB0LD_1RC1RB_0RE1LA_0RC0LA_1RF1RD_1LD---") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 3 3200 2 4 2 0). Qed.

Lemma recovered_held_2800_perm :
  Perm (flip recovered_held_2800) recovered_held_2800_reflected (fun q => q).
Proof.
  split.
  - intros q s H. destruct q,s; exact H.
  - intros q s w d q' H. destruct q,s; exact H.
Qed.

Theorem recovered_held_2800_nonhalt : ~ halts recovered_held_2800 c0.
Proof.
  intros [n Hn].
  apply recovered_held_2800_far.
  exists n.
  pose proof (flip_halts_in recovered_held_2800 c0 n Hn) as Hf.
  change (halts_in (flip recovered_held_2800) (A,tape0) n) in Hf.
  exact (@perm_halts_in _ _ _ A tape0 n recovered_held_2800_perm Hf).
Qed.

Theorem recovered_held_2800_safe bound : source_table_safe bound recovered_held_2800.
Proof. apply source_nonhalt_cylinder, recovered_held_2800_nonhalt. Qed.
Print Assumptions recovered_held_2800_safe.
