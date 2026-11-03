(* Original BusyCoq source-connected rooted halting proof transfers.
   Pin: ccz181078/busycoq 33209bc7dc282b38c8cd6be507bfc551fea56108.
   Uses ONLY pointwise finite-table Perm and source Flip, no functional
   extensionality or table equality axiom. No exact numerical score claim. *)

From BusyCoq Require Import Individual62 Others_v3.
Module F := Flip BB62.

Module OctoberRoot311.
Definition tm := Eval compute in (TM_from_str
  "1RB1RE_1LC0RD_1LD0LD_1RA0LC_0LB0RF_0RA---").

Lemma literal_mirror: Perm tm (F.flip TM7.tm) (fun q => q).
Proof.
  split.
  - intros q s H; destruct q,s; cbn in *; congruence.
  - intros q s s' d q' H; destruct q,s; cbn in H; try discriminate;
      inversion H; subst; reflexivity.
Qed.

Theorem raw_steps_preserved (n:nat):
  halts_in TM7.tm c0 n -> halts_in tm c0 n.
Proof.
  intro H.
  pose proof (@F.flip_halts_in TM7.tm c0 n H) as M.
  change (halts_in (F.flip TM7.tm) c0 n) in M.
  exact (@perm_halts_in' tm (F.flip TM7.tm)
    (fun q=>q) A tape0 n literal_mirror M).
Qed.

Theorem halts: halts tm c0.
Proof.
  apply (@perm_halts' tm (F.flip TM7.tm)
    (fun q=>q) A tape0 literal_mirror).
  change (halts (F.flip TM7.tm) (F.flip_conf c0)).
  exact (@F.flip_halts TM7.tm c0 TM7.halt).
Qed.
End OctoberRoot311.

Module OctoberMirror6.
Definition tm := Eval compute in (TM_from_str
  "1RB0LD_1RC1RE_1LD0RA_1LA0LA_0LC0RF_0RB---").

Lemma literal_mirror: Perm tm (F.flip TM6.tm) (fun q => q).
Proof.
  split.
  - intros q s H; destruct q,s; cbn in *; congruence.
  - intros q s s' d q' H; destruct q,s; cbn in H; try discriminate;
      inversion H; subst; reflexivity.
Qed.

Theorem halts: halts tm c0.
Proof.
  apply (@perm_halts' tm (F.flip TM6.tm)
    (fun q=>q) A tape0 literal_mirror).
  change (halts (F.flip TM6.tm) (F.flip_conf c0)).
  exact (@F.flip_halts TM6.tm c0 TM6.halt).
Qed.
End OctoberMirror6.

Print Assumptions OctoberRoot311.halts.
Print Assumptions OctoberRoot311.raw_steps_preserved.
Print Assumptions OctoberMirror6.halts.
