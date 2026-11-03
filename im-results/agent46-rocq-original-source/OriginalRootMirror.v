(* Primary-source rooted transfer of two October 2026 reported six-state halts.
   Original BusyCoq pinned at 33209bc7dc282b38c8cd6be507bfc551fea56108.
   This file imports and NEVER replaces the original TM7/TM6 halting proofs.
   Exact raw step counts are not obtained from these existential theorems. *)

From Coq Require Import Logic.FunctionalExtensionality.
From BusyCoq Require Import Individual62 Others_v3.
Module F := Flip BB62.

Module OctoberRoot311.
Definition tm := Eval compute in (TM_from_str
  "1RB1RE_1LC0RD_1LD0LD_1RA0LC_0LB0RF_0RA---").

Lemma literal_mirror: tm = F.flip TM7.tm.
Proof.
  apply functional_extensionality.
  intros [q s].
  destruct q, s; reflexivity.
Qed.

Theorem raw_steps_preserved (n:nat):
  halts_in TM7.tm c0 n -> halts_in tm c0 n.
Proof.
  intro H.
  rewrite literal_mirror.
  change c0 with (F.flip_conf c0).
  exact (F.flip_halts_in TM7.tm c0 n H).
Qed.

Theorem halts: halts tm c0.
Proof.
  rewrite literal_mirror.
  change c0 with (F.flip_conf c0).
  exact (F.flip_halts TM7.tm c0 TM7.halt).
Qed.
End OctoberRoot311.

Module OctoberMirror6.
Definition tm := Eval compute in (TM_from_str
  "1RB0LD_1RC1RE_1LD0RA_1LA0LA_0LC0RF_0RB---").

Lemma literal_mirror: tm = F.flip TM6.tm.
Proof.
  apply functional_extensionality.
  intros [q s].
  destruct q, s; reflexivity.
Qed.

Theorem halts: halts tm c0.
Proof.
  rewrite literal_mirror.
  change c0 with (F.flip_conf c0).
  exact (F.flip_halts TM6.tm c0 TM6.halt).
Qed.
End OctoberMirror6.

Print Assumptions OctoberRoot311.halts.
Print Assumptions OctoberRoot311.raw_steps_preserved.
Print Assumptions OctoberMirror6.halts.
