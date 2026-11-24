/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in upstream LICENSE.
Count-indexed variants of original dispatcher proofs at 3647718b5df22e1a61462dec0376bd204526285a.
Source-import compilation required before use as a proof.
-/
import RleDispatchCosts

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RleStackEngine
open BB6.Agent17.RleCost (weight drBot drBotZeros sweep drOne drZeros rnilOne rnilPow p1One p1Pow p2One p2Pow)
namespace BB6.Agent17.RleCounted

variable {target_tm : Machine (Fin 2) (Fin 6)} [CountedRules target_tm]

def CanHaltAt (M : Machine (Fin 2) (Fin 6)) (c : Cfg (Fin 2) (Fin 6)) (n : Nat) : Prop :=
  ∃ cfg, ReachesIn M n c cfg ∧ (step M cfg).isNone

def StateHaltsAt (M : Machine (Fin 2) (Fin 6)) (s : RleFullState) (n : Nat) : Prop :=
  if s.halted then n = 0 else CanHaltAt M (evalRle M s) n

theorem canHaltAt_of_reach {c c' : Cfg (Fin 2) (Fin 6)} {k n : Nat}
    (h : ReachesIn target_tm k c c') (hh : CanHaltAt target_tm c' n) :
    CanHaltAt target_tm c (k+n) := by
  obtain ⟨cfg,h2,hnone⟩ := hh
  exact ⟨cfg, ReachesIn.trans h h2, hnone⟩

theorem stateHaltsAt_of_reach {c : Cfg (Fin 2) (Fin 6)} {s' : RleFullState} {k n : Nat}
    (hf : s'.halted = false)
    (hstep : ReachesIn target_tm k c (evalRle target_tm s'))
    (hh : StateHaltsAt target_tm s' n) : CanHaltAt target_tm c (k+n) := by
  apply canHaltAt_of_reach hstep
  simpa [StateHaltsAt, hf] using hh

-- Reduce only the cost component, preserving the original configuration goal.
macro "countPrep" : tactic => `(tactic| (
  conv => arg 3; arg 1; try simp [costRawB, costRawBRPop, costRawBR, costRawDR0Atomic, costRawDR0, costRawCAtomic, costRawC, costCleanBPop, costRNIL, costCleanB, costCleanBR, costCleanDR0, costRleStep, *]))

macro "countTransfer" hh:term : tactic => `(tactic| (
  countPrep
  refine stateHaltsAt_of_reach rfl ?_ $hh))

macro "countUse" t:term : tactic => `(tactic| (
  countPrep
  first
  | exact $t
  | simpa [costRawB, costRawBRPop, costRawBR, costRawDR0Atomic, costRawDR0, costRawCAtomic, costRawC, costCleanBPop, costRNIL, costCleanB, costCleanBR, costCleanDR0, costRleStep, *] using $t))

theorem c_stepRawB_halts (items R : List Item) (n : Nat) (hh : StateHaltsAt target_tm (stepRawB items R) n) :
    CanHaltAt target_tm (cfg_B target_tm (decL items) (decR R)) (costRawB items R+n) := by
  unfold stepRawB at hh
  cases R with
  | nil =>
    countTransfer hh
    simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
      id (c_rule_B_nil (decL items))
  | cons hd R1 =>
    cases hd with
    | z c =>
      countTransfer hh
      simpa [evalRle, evalStackCfg1, decLState, decL_pushL0, decR] using
        c_rule_B_zeros_all (decL items) (decR R1) c
    | d v =>
      dsimp only at hh
      cases hp : popR1 (.d v :: R1) with
      | none => cases hp
      | some p =>
        rcases p with ⟨d, R2⟩
        rw [hp] at hh
        have hR := decR_popR1_some _ d R2 hp
        dsimp only at hh; split at hh
        · next hd0 =>
          rw [Nat.beq_eq] at hd0; subst hd0
          countTransfer hh
          rw [hR]
          simpa [evalRle, evalStackCfg1, decLState, decL_pushL0] using
            id (c_rule_B_zero (decL items) (decR R2))
        · next hd0 =>
          have hdne : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
          countTransfer hh
          rw [hR, show d = (d - 1) + 1 by omega]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0, decR_pushRd]
              using
            id (c_rule_B_succ (d - 1) (decL items) (decR R2))
    | k r c =>
      dsimp only at hh
      cases hp : popR1 (.k r c :: R1) with
      | none =>
        rw [hp] at hh
        countTransfer hh
        rw [decR_popR1_none _ hp]
        simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
          id (c_rule_B_nil (decL items))
      | some p =>
        rcases p with ⟨d, R2⟩
        rw [hp] at hh
        have hR := decR_popR1_some _ d R2 hp
        dsimp only at hh; split at hh
        · next hd0 =>
          rw [Nat.beq_eq] at hd0; subst hd0
          countTransfer hh
          rw [hR]
          simpa [evalRle, evalStackCfg1, decLState, decL_pushL0] using
            id (c_rule_B_zero (decL items) (decR R2))
        · next hd0 =>
          have hdne : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
          countTransfer hh
          rw [hR, show d = (d - 1) + 1 by omega]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0, decR_pushRd]
              using
            id (c_rule_B_succ (d - 1) (decL items) (decR R2))

theorem c_stepRawBRPop_halts (items R : List Item) (n : Nat) (hh : StateHaltsAt target_tm (stepRawBRPop items
    R) n) :
    CanHaltAt target_tm (cfg_BR target_tm (decL items) (decR R)) (costRawBRPop items R+n) := by
  unfold stepRawBRPop at hh
  cases hp : popR1 R with
  | none =>
    rw [hp] at hh
    countTransfer hh
    rw [decR_popR1_none R hp]
    simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
      id (c_rule_BR_nil (decL items))
  | some p =>
    rcases p with ⟨d, R1⟩
    rw [hp] at hh
    have hR := decR_popR1_some R d R1 hp
    dsimp only at hh; split at hh
    · next hd0 =>
      rw [Nat.beq_eq] at hd0; subst hd0
      countTransfer hh
      rw [hR]
      simpa [evalRle, evalStackCfg1, decLState, decL_pushL0] using
        id (c_rule_BR_zero (decL items) (decR R1))
    · next hd0 =>
      have hdne0 : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
      split at hh
      · next hd1 =>
        rw [Nat.beq_eq] at hd1; subst hd1
        countTransfer hh
        rw [hR]
        simpa [evalRle, evalStackCfg1, decLState, decR_bumpR] using
          id (c_rule_BR_one (decL items) (decR R1))
      · next hd1 =>
        have hdne1 : d ≠ 1 := fun h => hd1 (Nat.beq_eq.mpr h)
        countTransfer hh
        rw [hR, show d = (d - 2) + 2 by omega]
        simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR_pushRd]
            using
          id (c_rule_BR_add_two (d - 2) (decL items) (decR R1))

theorem c_stepRawBR_halts (items R : List Item) (n : Nat) (hh : StateHaltsAt target_tm (stepRawBR items R) n) :
    CanHaltAt target_tm (cfg_BR target_tm (decL items) (decR R)) (costRawBR items R+n) := by
  unfold stepRawBR at hh
  cases R with
  | nil =>
    countTransfer hh
    simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR] using
      id (c_rule_BR_nil (decL items))
  | cons hd R1 =>
    cases hd with
    | z c =>
      countTransfer hh
      simpa [evalRle, evalStackCfg1, decLState, decL_pushL0, decR] using
        c_rule_BR_zeros_all (decL items) (decR R1) c
    | d v => countUse c_stepRawBRPop_halts items (.d v :: R1) n hh
    | k r m =>
      dsimp only at hh; split at hh
      · next hm1 =>
        have hmge : 1 ≤ m := Nat.ble_eq.mp hm1
        cases hpL : popL1 items with
        | none =>
          rw [hpL] at hh
          countUse c_stepRawBRPop_halts items (.k r m :: R1) n hh
        | some pL =>
          rcases pL with ⟨a, L1⟩
          rw [hpL] at hh; dsimp only at hh; split at hh
          · next ha0 =>
            rw [Nat.beq_eq] at ha0; subst ha0
            countTransfer hh
            rw [decL_popL1_some items 0 L1 hpL, decR, show m = (m - 1) + 1 by omega]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushL0,
                decL_pushLd,
              decL_pushLk2, List.append_assoc] using
              c_rule_BR_blkR_succ (m - 1) r (decL L1) (decR R1)
          · countUse c_stepRawBRPop_halts items (.k r m :: R1) n hh
      · next hm0 =>
        have hmeq : m = 0 := by
          have : ¬ 1 ≤ m := fun h => hm0 (Nat.ble_eq.mpr h); omega
        subst hmeq
        countTransfer hh
        exact ReachesIn.zero _ _

theorem c_stepRawDR0Atomic_halts (items R : List Item) (n : Nat) (hh : StateHaltsAt target_tm (stepRawDR0Atomic
    items R) n) :
    CanHaltAt target_tm (cfg_DR0 target_tm (decL items) (decR R)) (costRawDR0Atomic items R+n) := by
  unfold stepRawDR0Atomic at hh
  cases hpL : popL1 items with
  | none =>
    rw [hpL] at hh
    countTransfer hh
    rw [decL_popL1_none items hpL]
    simpa [evalRle, evalStackCfg1, decLState, decL] using
      id (c_rule_DR0_nil (decR R))
  | some pL =>
    rcases pL with ⟨a, L1⟩
    rw [hpL] at hh
    have hL := decL_popL1_some items a L1 hpL
    dsimp only at hh; split at hh
    · next ha0 =>
      rw [Nat.beq_eq] at ha0; subst ha0
      cases items with
      | nil => cases hpL
      | cons hd Lrest =>
        cases hd with
        | z c =>
          countTransfer hh
          simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushR0] using
            c_rule_DR0_zeros_all (decL Lrest) (decR R) c
        | d _ =>
          countTransfer hh
          rw [hL]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0] using
            id (c_rule_DR0_zero (decL L1) (decR R))
        | k _ _ =>
          countTransfer hh
          rw [hL]
          simpa [evalRle, evalStackCfg1, decLState, decR_pushR0] using
            id (c_rule_DR0_zero (decL L1) (decR R))
    · next ha0 =>
      have hane : a ≠ 0 := fun h => ha0 (Nat.beq_eq.mpr h)
      countTransfer hh
      rw [hL, show a = (a - 1) + 1 by omega]
      simpa [evalRle, evalStackCfg1, decLState, decL_pushLd, decR_pushR0]
          using
        id (c_rule_DR0_succ (a - 1) (decL L1) (decR R))

theorem c_stepRawDR0_halts (items R : List Item) (n : Nat) (hh : StateHaltsAt target_tm (stepRawDR0 items R) n) :
    CanHaltAt target_tm (cfg_DR0 target_tm (decL items) (decR R)) (costRawDR0 items R+n) := by
  unfold stepRawDR0 at hh
  rcases items with _ | ⟨hd1, _ | ⟨hd2, xs⟩⟩
  · countUse c_stepRawDR0Atomic_halts [] R n hh
  · cases hd1 with
    | z c =>
      have hbot : ∀ (hhb : StateHaltsAt target_tm ⟨.BR, .raw [.z (c + 3)], R, false⟩ n),
          CanHaltAt target_tm (cfg_DR0 target_tm (decL [.z c]) (decR R)) (drBot c+n) := by
        intro hhb
        countTransfer hhb
        simpa [evalRle, evalStackCfg1, decLState, decL] using c_rule_DR0_bot c
            (decR R)
      rcases R with _ | ⟨r1, _ | ⟨r2, R2⟩⟩
      · countUse hbot hh
      · cases r1 <;> countUse hbot hh
      · cases r1 with
        | d v1 =>
          cases r2 with
          | z q =>
            dsimp only at hh; split at hh
            · next hv1 =>
              rw [Nat.beq_eq] at hv1; subst hv1
              countTransfer hh
              simpa [evalRle, evalStackCfg1, decLState, decL, decR] using
                c_rule_DR0_bot_zeros q c (decR R2)
            · countUse hbot hh
          | _ => countUse hbot hh
        | _ => countUse hbot hh
    | d _ => countUse c_stepRawDR0Atomic_halts _ R n hh
    | k _ _ => countUse c_stepRawDR0Atomic_halts _ R n hh
  · cases hd1 <;> countUse c_stepRawDR0Atomic_halts _ R n hh

theorem c_stepRawCAtomic_halts (items R : List Item) (n : Nat) (hh : StateHaltsAt target_tm (stepRawCAtomic
    items R) n) :
    CanHaltAt target_tm (cfg_C target_tm (decL items) (decR R)) (costRawCAtomic items R+n) := by
  unfold stepRawCAtomic at hh
  cases hp1 : popL1 items with
  | none =>
    rw [hp1] at hh
    countTransfer hh
    rw [decL_popL1_none items hp1]
    exact id (c_rule_C_nil _)
  | some p1 =>
    rcases p1 with ⟨a, L1⟩
    rw [hp1] at hh
    have hL1 := decL_popL1_some items a L1 hp1
    dsimp only at hh; split at hh
    · next ha0 =>
      rw [Nat.beq_eq] at ha0; subst ha0
      cases hp2 : popL1 L1 with
      | none =>
        rw [hp2] at hh
        countTransfer hh
        rw [hL1, decL_popL1_none L1 hp2]
        simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushRd] using
          id (c_rule_C_zero_nil (decR R))
      | some p2 =>
        rcases p2 with ⟨a1, L3⟩
        rw [hp2] at hh
        have hL2 := decL_popL1_some L1 a1 L3 hp2
        dsimp only at hh; split at hh
        · next ha10 =>
          rw [Nat.beq_eq] at ha10; subst ha10
          countTransfer hh
          rw [hL1, hL2]
          simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR_pushRd]
              using
            id (c_rule_C_zero_zero (decL L3) (decR R))
        · next ha10 =>
          have hne0 : a1 ≠ 0 := fun h => ha10 (Nat.beq_eq.mpr h)
          split at hh
          · next ha11 =>
            rw [Nat.beq_eq] at ha11; subst ha11
            countTransfer hh
            rw [hL1, hL2]
            simpa [evalRle, evalStackCfg1, decLState, decL_bumpL, decR_pushR0
                , decR_bumpR] using
              id (c_rule_C_zero_one (decL L3) (decR R))
          · next ha11 =>
            have hne1 : a1 ≠ 1 := fun h => ha11 (Nat.beq_eq.mpr h)
            countTransfer hh
            rw [hL1, hL2, show a1 = (a1 - 2) + 2 by omega]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushLd, decR_pushR0
                , decR_pushRd] using
              id (c_rule_C_zero_add_two (a1 - 2) (decL L3) (decR R))
    · next ha0 =>
      have hane0 : a ≠ 0 := fun h => ha0 (Nat.beq_eq.mpr h)
      split at hh
      · next ha1 =>
        rw [Nat.beq_eq] at ha1; subst ha1
        cases hp2 : popL1 L1 with
        | none =>
          rw [hp2] at hh
          countTransfer hh
          rw [hL1, decL_popL1_none L1 hp2]
          simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushRd] using
            id (c_rule_C_one_nil (decR R))
        | some p2 =>
          rcases p2 with ⟨a1, L3⟩
          rw [hp2] at hh
          have hL2 := decL_popL1_some L1 a1 L3 hp2
          dsimp only at hh; split at hh
          · next ha10 =>
            rw [Nat.beq_eq] at ha10; subst ha10
            countTransfer hh
            rw [hL1, hL2]
            simpa [evalRle, evalStackCfg1, decLState, decR_pushRd] using
              id (c_rule_C_one_zero (decL L3) (decR R))
          · next ha10 =>
            have hne0 : a1 ≠ 0 := fun h => ha10 (Nat.beq_eq.mpr h)
            countTransfer hh
            rw [hL1, hL2, show a1 = (a1 - 1) + 1 by omega]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushLd,
                decR_pushRd] using
              id (c_rule_C_one_succ (a1 - 1) (decL L3) (decR R))
      · next ha1 =>
        have hane1 : a ≠ 1 := fun h => ha1 (Nat.beq_eq.mpr h)
        countPrep
        have hn : n = 0 := by simpa [StateHaltsAt] using hh
        subst n
        rw [hL1, show a = (a - 2) + 2 by omega]
        obtain ⟨cfg', hstep, hnone⟩ :=
          c_rule_C_add_two_halt (target_tm := target_tm) (a - 2) (decL L1) (decR R)
        exact ⟨cfg', id hstep, hnone⟩

theorem c_stepRawC_halts (items R : List Item) (n : Nat) (hh : StateHaltsAt target_tm (stepRawC items R) n) :
    CanHaltAt target_tm (cfg_C target_tm (decL items) (decR R)) (costRawC items R+n) := by
  unfold stepRawC at hh
  rcases items with _ | ⟨hd1, rest1⟩
  · countUse c_stepRawCAtomic_halts [] R n hh
  · cases hd1 with
    | z cz =>
      rcases rest1 with _ | ⟨hd2, L2⟩
      · dsimp only at hh; split at hh
        · next h4 =>
          have hge4 : 4 ≤ cz := Nat.ble_eq.mp h4
          countTransfer hh
          have heq : decL [.z cz] = rep0 ((cz - 4) + 4) := by
            rw [decL, decL, List.append_nil, show cz - 4 + 4 = cz by omega]
          rw [heq]
          simpa [evalRle, evalStackCfg1, decLState, decL, decR_pushRk2,
            HPow.hPow, List.append_eq] using
            c_rule_C_bot_four (cz - 4) (decR R)
        · countUse c_stepRawCAtomic_halts [.z cz] R n hh
      · cases hd2 with
        | k r m =>
          dsimp only at hh; split at hh
          · next hcz =>
            rw [Nat.beq_eq] at hcz; subst hcz
            countTransfer hh
            simpa [evalRle, evalStackCfg1, decLState, decL, decL_pushL0,
                decR_pushRk2] using
              c_rule_C_blkL_pow m r (decL L2) (decR R)
          · countUse c_stepRawCAtomic_halts _ R n hh
        | d v1 =>
          dsimp only at hh; split at hh
          · next hb =>
            simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hb
            rcases hb with ⟨hge4, rfl⟩
            countTransfer hh
            have heq : decL (.z cz :: .d 1 :: L2) = rep0 ((cz - 3) + 3) ++ 1 :: decL L2 := by
              rw [decL, decL, show cz - 3 + 3 = cz by omega]
            rw [heq]
            simpa [evalRle, evalStackCfg1, decLState, decL_pushL0,
                decR_pushRk2,
              HPow.hPow, List.append_eq] using
              c_rule_C_r_add_three (cz - 3) (decL L2) (decR R)
          · countUse c_stepRawCAtomic_halts _ R n hh
        | z _ => countUse c_stepRawCAtomic_halts _ R n hh
    | d _ => countUse c_stepRawCAtomic_halts _ R n hh
    | k _ _ => countUse c_stepRawCAtomic_halts _ R n hh

theorem c_stepCleanBPop_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (n : Nat) (hh : StateHaltsAt target_tm (stepCleanBPop c0 segs bot R) n) :
    CanHaltAt target_tm (cfg_B target_tm (decLState (.clean c0 segs bot)) (decR R)) (costCleanBPop c0 segs bot R+n) := by
  unfold stepCleanBPop at hh
  cases hp : popR1 R with
  | none =>
    rw [hp] at hh
    countTransfer hh
    simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
  | some p =>
    rcases p with ⟨d, R1⟩
    rw [hp] at hh
    have hR := decR_popR1_some R d R1 hp
    dsimp only at hh; split at hh
    · next hd0 =>
      rw [Nat.beq_eq] at hd0; subst hd0
      countTransfer hh
      rw [hR]
      have heq : 0 :: decLState (.clean c0 segs bot) = decLState (.clean (c0 + 1) segs bot) := by
        countNormAll
      simpa [evalRle, evalStackCfg1, ← heq] using
        id (c_rule_B_zero (decLState (.clean c0 segs bot)) (decR R1))
    · next hd0 =>
      have hdne : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
      countTransfer hh
      rw [hR, show d = (d - 1) + 1 by omega]
      simpa [evalRle, evalStackCfg1, decR_pushR0, decR_pushRd] using
        id (c_rule_B_succ (d - 1) (decLState (.clean c0 segs bot)) (decR R1))

theorem c_stepCleanB_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (n : Nat) (hh : StateHaltsAt target_tm (stepCleanB c0 segs bot R) n) :
    CanHaltAt target_tm (cfg_B target_tm (decLState (.clean c0 segs bot)) (decR R)) (costCleanB c0 segs bot R+n) := by
  unfold stepCleanB at hh
  rcases R with _ | ⟨hd1, R1⟩
  · dsimp only at hh; split at hh
    · next hb =>
      simp only [Bool.and_eq_true, Nat.ble_eq] at hb
      rcases hb with ⟨hc0, hbot⟩
      countTransfer hh
      have h1 := c_clean_RNIL_one (target_tm := target_tm) .B (Or.inl rfl) (c0 - 1) segs (bot - 1)
      have h2 := c_clean_RNIL_zero_pow (target_tm := target_tm) (bot - 1) (pushSeg (c0 - 1) 1 segs) 0
      rw [show c0 - 1 + 1 = c0 by omega, show bot - 1 + 1 = bot by omega] at h1
      rw [show 0 + (bot - 1) = bot - 1 by omega] at h2
      countExact ReachesIn.trans h1 h2
    · countTransfer hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
  · cases hd1 with
    | z cz =>
      have h_zonly : ∀ (Rtail : List Item)
          (hhz : StateHaltsAt target_tm ⟨.B, .clean (c0 + cz) segs bot, Rtail, false⟩ n),
          CanHaltAt target_tm (cfg_B target_tm (decLState (.clean c0 segs bot)) (decR (.z cz ::
              Rtail))) (4*cz+n) := by
        intro Rtail hhz
        countTransfer hhz
        have hstep := c_rule_B_zeros_all (target_tm := target_tm)
            (decLState (.clean c0 segs bot)) (decR Rtail) cz
        have heq : rep0 cz ++ decLState (.clean c0 segs bot) =
            decLState (.clean (c0 + cz) segs bot) := by
          rw [Nat.add_comm c0 cz]; countNormAll
        rw [heq] at hstep
        countExact hstep
      rcases R1 with _ | ⟨hd2, Rrem⟩
      · countUse h_zonly [] hh
      · cases hd2 with
        | k r cnt =>
          dsimp only at hh; split at hh
          · next hb =>
            simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
            rcases hb with ⟨⟨rfl, hbot⟩, rfl⟩
            split at hh
            · next hq1 =>
              set q := minNat cnt bot
              have hqge : 1 ≤ minNat cnt bot := Nat.ble_eq.mp hq1
              have hqcnt : q ≤ cnt := minNat_le_left cnt bot
              have hqbot : q ≤ bot := minNat_le_right cnt bot
              countTransfer hh
              have hstep := c_clean_P1_pow (target_tm := target_tm) q r segs (bot - q)
                  ((blkR r) ^ (cnt - q) ++ decR Rrem)
              rw [show bot - q + q = bot by omega] at hstep
              have heqR1 : 0 :: ((blkR r) ^ q ++ ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                  decR (.z 1 :: .k r cnt :: Rrem) := by
                rw [← List.append_assoc, ← list_pow_add, show q + (cnt - q) = cnt by omega]
                countNormAll
              have heqR2 : (0 :: ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                  decR (if Nat.beq cnt q then .z 1 :: Rrem else .z 1 :: .k r (cnt - q) :: Rrem) :=
                      by
                split
                · next heq => rw [Nat.beq_eq] at heq; rw [heq, Nat.sub_self]; countNormAll
                · countNormAll
              rw [heqR1, heqR2] at hstep
              countExact hstep
            · countUse h_zonly _ hh
          · countUse h_zonly _ hh
        | _ => countUse h_zonly _ hh
    | d v1 =>
      rcases R1 with _ | ⟨hd2, _ | ⟨hd3, Rrem⟩⟩
      · countUse c_stepCleanBPop_halts c0 segs bot _ n hh
      · cases hd2 <;> countUse c_stepCleanBPop_halts c0 segs bot _ n hh
      · cases hd2 with
        | d v2 =>
          cases hd3 with
          | k r cnt =>
            dsimp only at hh; split at hh
            · next hb =>
              simp only [Bool.and_eq_true, Nat.beq_eq] at hb
              rcases hb with ⟨⟨rfl, rfl⟩, rfl⟩
              split at hh
              · next hq1 =>
                set q := minNat cnt (bot / (r + 1))
                have hqge : 1 ≤ minNat cnt (bot / (r + 1)) := Nat.ble_eq.mp hq1
                have hqcnt : q ≤ cnt := minNat_le_left cnt _
                have hqdiv : q ≤ bot / (r + 1) := minNat_le_right cnt _
                have hqmul : q * (r + 1) ≤ bot :=
                  Nat.le_trans (Nat.mul_le_mul_right (r + 1) hqdiv) (Nat.div_mul_le_self bot (r +
                      1))
                countTransfer hh
                have hstep := c_clean_P2_pow (target_tm := target_tm) q r segs (bot - q * (r + 1))
                    ((blkR r) ^ (cnt - q) ++ decR Rrem)
                rw [show bot - q * (r + 1) + q * (r + 1) = bot by omega] at hstep
                have heqR1 : 1 :: 1 :: ((blkR r) ^ q ++ ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                    decR (.d 1 :: .d 1 :: .k r cnt :: Rrem) := by
                  rw [← List.append_assoc, ← list_pow_add, show q + (cnt - q) = cnt by omega]
                  countNormAll
                have heqR2 : (1 :: 1 :: ((blkR r) ^ (cnt - q) ++ decR Rrem)) =
                    decR (if Nat.beq cnt q then .d 1 :: .d 1 :: Rrem else .d 1 :: .d 1 :: .k r
                        (cnt - q) :: Rrem) := by
                  split
                  · next heq => rw [Nat.beq_eq] at heq; rw [heq, Nat.sub_self]; countNormAll
                  · countNormAll
                rw [heqR1, heqR2] at hstep
                countExact hstep
              · countTransfer hh
                simpa [evalRle, evalStackCfg1, decR_pushR0, decR_pushRd, decR]
                    using
                  id (c_rule_B_succ 0 (decLState (.clean 0 segs bot)) (decR (.d 1 ::
                      .k r cnt :: Rrem)))
            · countUse c_stepCleanBPop_halts c0 segs bot _ n hh
          | _ => countUse c_stepCleanBPop_halts c0 segs bot _ n hh
        | _ => countUse c_stepCleanBPop_halts c0 segs bot _ n hh
    | k _ _ => countUse c_stepCleanBPop_halts c0 segs bot _ n hh

theorem c_stepCleanBR_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (n : Nat) (hh : StateHaltsAt target_tm (stepCleanBR c0 segs bot R) n) :
    CanHaltAt target_tm (cfg_BR target_tm (decLState (.clean c0 segs bot)) (decR R)) (costCleanBR c0 segs bot R+n) := by
  unfold stepCleanBR at hh
  rcases R with _ | ⟨hd1, R1⟩
  · dsimp only at hh; split at hh
    · next hb =>
      simp only [Bool.and_eq_true, Nat.ble_eq] at hb
      rcases hb with ⟨hc0, hbot⟩
      countTransfer hh
      have h1 := c_clean_RNIL_one (target_tm := target_tm) .BR (Or.inr rfl) (c0 - 1) segs (bot - 1)
      have h2 := c_clean_RNIL_zero_pow (target_tm := target_tm) (bot - 1) (pushSeg (c0 - 1) 1 segs) 0
      rw [show c0 - 1 + 1 = c0 by omega, show bot - 1 + 1 = bot by omega] at h1
      rw [show 0 + (bot - 1) = bot - 1 by omega] at h2
      countExact ReachesIn.trans h1 h2
    · countTransfer hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
  · cases hd1 with
    | z cz =>
      countTransfer hh
      have hstep := c_rule_BR_zeros_all (target_tm := target_tm)
          (decLState (.clean c0 segs bot)) (decR R1) cz
      have heq : rep0 cz ++ decLState (.clean c0 segs bot) =
          decLState (.clean (c0 + cz) segs bot) := by
        rw [Nat.add_comm c0 cz]; countNormAll
      rw [heq] at hstep
      countExact hstep
    | k r m =>
      dsimp only at hh; split at hh
      · next hb =>
        simp only [Bool.and_eq_true, Nat.ble_eq] at hb
        rcases hb with ⟨⟨hm, hc0⟩, hrc⟩
        countTransfer hh
        have heqL0 : decLState (.clean c0 segs bot) =
            0 :: (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) := by
          conv_lhs => rw [decLState, show c0 = (c0 - 1) + 1 by omega]
          countNormAll
        have hstep := c_rule_BR_blkR_succ (target_tm := target_tm) (m - 1) r
            (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) (decR R1)
        have heqR : decR (.k r m :: R1) = (blkR r) ^ ((m - 1) + 1) ++ decR R1 := by
          rw [decR, show m - 1 + 1 = m by omega]
        have heqL1 : rep0 3 ++ 1 :: ((blkL r) ^ (m - 1) ++ (rep0 r ++ (rep0 (c0 - 1) ++ 1 ::
            (decSegs segs ++ rep0 (bot + 2))))) =
            decLState (.clean 3 (pushSeg r (m - 1) (pushSeg (r + c0 - 3) 1 segs)) bot) := by
          have hmerge : rep0 r ++ (rep0 (c0 - 1) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
              rep0 ((r + c0 - 3) + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)) := by
            rw [← List.append_assoc, ← rep0_add_split, show r + (c0 - 1) = (r + c0 - 3) + 2 by
                omega]
          rw [hmerge]
          countNormAll
        dsimp only [evalRle, evalStackCfg1]
        rw [heqL0, heqR, ← heqL1]
        refine reindex hstep ?_
        rw [show m - 1 + 1 = m by omega]
      · countTransfer hh
        simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]
    | d v =>
      dsimp only at hh
      cases hp : popR1 (.d v :: R1) with
      | none => cases hp
      | some p =>
        rcases p with ⟨d, R2⟩
        rw [hp] at hh
        have hR := decR_popR1_some _ d R2 hp
        dsimp only at hh; split at hh
        · next hd0 =>
          rw [Nat.beq_eq] at hd0; subst hd0
          countTransfer hh
          rw [hR]
          have heq : 0 :: decLState (.clean c0 segs bot) = decLState (.clean (c0 + 1) segs bot) :=
              by
            countNormAll
          simpa [evalRle, evalStackCfg1, ← heq] using
            id (c_rule_BR_zero (decLState (.clean c0 segs bot)) (decR R2))
        · next hd0 =>
          have hdne0 : d ≠ 0 := fun h => hd0 (Nat.beq_eq.mpr h)
          split at hh
          · next hd1 =>
            rw [Nat.beq_eq] at hd1; subst hd1
            countTransfer hh
            rw [hR]
            simpa [evalRle, evalStackCfg1, decR_bumpR] using
              id (c_rule_BR_one (decLState (.clean c0 segs bot)) (decR R2))
          · next hd1 =>
            have hdne1 : d ≠ 1 := fun h => hd1 (Nat.beq_eq.mpr h)
            split at hh
            · next hc3 =>
              have hcge : 3 ≤ c0 := Nat.ble_eq.mp hc3
              countTransfer hh
              rw [hR, show d = (d - 2) + 2 by omega]
              have hstep := id (c_rule_BR_add_two (target_tm := target_tm) (d - 2)
                  (decLState (.clean c0 segs bot)) (decR R2))
              have heq : bumpHead (decLState (.clean c0 segs bot)) =
                  decLState (.clean 0 (pushSeg (c0 - 3) 1 segs) bot) := by
                conv_lhs => rw [decLState, show c0 = (c0 - 3) + 3 by omega]
                countNormAll
              rw [heq] at hstep
              simpa [evalRle, evalStackCfg1, decR_pushRd] using hstep
            · countTransfer hh
              simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

theorem c_stepCleanDR0_halts (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item)
    (n : Nat) (hh : StateHaltsAt target_tm (stepCleanDR0 c0 segs bot R) n) :
    CanHaltAt target_tm (cfg_DR0 target_tm (decLState (.clean c0 segs bot)) (decR R)) (costCleanDR0 c0 segs bot R+n) := by
  unfold stepCleanDR0 at hh
  split at hh
  · next hbot =>
    have hbge : 1 ≤ bot := Nat.ble_eq.mp hbot
    have h_one : ∀ (hh1 : StateHaltsAt target_tm ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩ n),
        CanHaltAt target_tm (cfg_DR0 target_tm (decLState (.clean c0 segs bot)) (decR R)) (drOne c0 (bot-1) (weight segs)+n) := by
      intro hh1
      countTransfer hh1
      have hstep := c_clean_DR0_one (target_tm := target_tm) c0 segs (bot - 1) (decR R)
      rw [show bot - 1 + 1 = bot by omega] at hstep
      countExact hstep
    rcases R with _ | ⟨r1, _ | ⟨r2, R2⟩⟩
    · countUse h_one hh
    · cases r1 <;> countUse h_one hh
    · cases r1 with
      | d v1 =>
        cases r2 with
        | z rz =>
          dsimp only at hh; split at hh
          · next hv1 =>
            rw [Nat.beq_eq] at hv1; subst hv1
            split at hh
            · next hq1 =>
              set q := minNat rz bot
              have hqge : 1 ≤ minNat rz bot := Nat.ble_eq.mp hq1
              have hqrz : q ≤ rz := minNat_le_left rz bot
              have hqbot : q ≤ bot := minNat_le_right rz bot
              countTransfer hh
              have hstep := c_clean_DR0_zeros (target_tm := target_tm) q c0 segs (bot - q)
                  (rep0 (rz - q) ++ decR R2)
              rw [show bot - q + q = bot by omega] at hstep
              have heqR1 : 1 :: (rep0 q ++ (rep0 (rz - q) ++ decR R2)) =
                  decR (.d 1 :: .z rz :: R2) := by
                rw [← List.append_assoc, ← rep0_add_split, show q + (rz - q) = rz by omega]
                countNormAll
              have heqR2 : (1 :: (rep0 (rz - q) ++ decR R2)) =
                  decR (if Nat.beq rz q then .d 1 :: R2 else .d 1 :: .z (rz - q) :: R2) := by
                split
                · next heq => rw [Nat.beq_eq] at heq; rw [heq, Nat.sub_self]; countNormAll
                · countNormAll
              rw [heqR1, heqR2] at hstep
              countExact hstep
            · countUse h_one hh
          · countUse h_one hh
        | _ => countUse h_one hh
      | _ => countUse h_one hh
  · countTransfer hh
    simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

theorem c_rleStep_halts (s : RleFullState) (n : Nat) (hh : StateHaltsAt target_tm (rleStep s) n) :
    CanHaltAt target_tm (evalRle target_tm s) (costRleStep s+n) := by
  rcases s with ⟨mode, ls, R, halted⟩
  unfold rleStep at hh
  dsimp only at hh
  cases ls with
  | raw items =>
    dsimp only at hh
    cases hpk : tryPack mode items R with
    | some ls' =>
      rw [hpk] at hh
      countTransfer hh
      simp [evalRle, decLState, tryPack_spec mode items R ls' hpk]
    | none =>
      rw [hpk] at hh
      cases mode with
      | B => 
        simpa only [costRleStep, hpk, evalRle, evalStackCfg1, decLState] using c_stepRawB_halts items R n hh
      | BR => 
        simpa only [costRleStep, hpk, evalRle, evalStackCfg1, decLState] using c_stepRawBR_halts items R n hh
      | DR0 => 
        simpa only [costRleStep, hpk, evalRle, evalStackCfg1, decLState] using c_stepRawDR0_halts items R n hh
      | C => 
        simpa only [costRleStep, hpk, evalRle, evalStackCfg1, decLState] using c_stepRawC_halts items R n hh
  | clean c0 segs bot =>
    dsimp only at hh
    cases mode with
    | B => 
        simpa only [costRleStep, evalRle, evalStackCfg1, decLState] using c_stepCleanB_halts c0 segs bot R n hh
    | BR => 
        simpa only [costRleStep, evalRle, evalStackCfg1, decLState] using c_stepCleanBR_halts c0 segs bot R n hh
    | DR0 => 
        simpa only [costRleStep, evalRle, evalStackCfg1, decLState] using c_stepCleanDR0_halts c0 segs bot R n hh
    | C =>
      countTransfer hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

end BB6.Agent17.RleCounted

#print axioms BB6.Agent17.RleCounted.c_rleStep_halts
