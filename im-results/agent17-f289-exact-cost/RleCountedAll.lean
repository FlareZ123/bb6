/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in upstream LICENSE.
Proof bodies derived from google-deepmind/cryptids @ 3647718b5df22e1a61462dec0376bd204526285a,
BusyBeaver/Calculi/HaltShared.lean. Only the reachability relation and
cost arithmetic are changed. Source-import compile is required.
-/
import RleCostAlgebra
import RleCountedAtoms

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RleStackEngine
open BB6.Agent17.RleCost (weight drBot drBotZeros sweep drOne drZeros rnilOne rnilPow p1One p1Pow p2One p2Pow)
namespace BB6.Agent17.RleCounted

local notation:50 a " [" m "]⊢ᶜ[" n "] " b => ReachesIn m n a b

variable {target_tm : Machine (Fin 2) (Fin 6)} [CountedRules target_tm]

abbrev c_rule_B_nil := CountedRules.rule_B_nil (target_tm := target_tm)
abbrev c_rule_B_zero := CountedRules.rule_B_zero (target_tm := target_tm)
abbrev c_rule_B_succ := CountedRules.rule_B_succ (target_tm := target_tm)
abbrev c_rule_BR_nil := CountedRules.rule_BR_nil (target_tm := target_tm)
abbrev c_rule_BR_zero := CountedRules.rule_BR_zero (target_tm := target_tm)
abbrev c_rule_BR_one := CountedRules.rule_BR_one (target_tm := target_tm)
abbrev c_rule_BR_add_two := CountedRules.rule_BR_add_two (target_tm := target_tm)
abbrev c_rule_DR0_nil := CountedRules.rule_DR0_nil (target_tm := target_tm)
abbrev c_rule_DR0_zero := CountedRules.rule_DR0_zero (target_tm := target_tm)
abbrev c_rule_DR0_succ := CountedRules.rule_DR0_succ (target_tm := target_tm)
abbrev c_rule_C_nil := CountedRules.rule_C_nil (target_tm := target_tm)
abbrev c_rule_C_zero_nil := CountedRules.rule_C_zero_nil (target_tm := target_tm)
abbrev c_rule_C_zero_zero := CountedRules.rule_C_zero_zero (target_tm := target_tm)
abbrev c_rule_C_zero_one := CountedRules.rule_C_zero_one (target_tm := target_tm)
abbrev c_rule_C_zero_add_two := CountedRules.rule_C_zero_add_two (target_tm := target_tm)
abbrev c_rule_C_one_nil := CountedRules.rule_C_one_nil (target_tm := target_tm)
abbrev c_rule_C_one_zero := CountedRules.rule_C_one_zero (target_tm := target_tm)
abbrev c_rule_C_one_succ := CountedRules.rule_C_one_succ (target_tm := target_tm)
abbrev c_rule_C_add_two_halt := CountedRules.rule_C_add_two_halt (target_tm := target_tm)

theorem sourceWeightPush (r c : Nat) (segs : List (Nat × Nat)) :
    weight (BusyBeaver.RleStackEngine.pushSeg r c segs) = c*(6*r+26)+weight segs :=
  BB6.Agent17.RleCost.weight_pushSeg r c segs

theorem weightNil : weight [] = 0 := rfl
theorem weightCons (r c : Nat) (segs : List (Nat × Nat)) :
    weight ((r,c)::segs) = c*(6*r+26)+weight segs := rfl

theorem reindex {M : Machine (Fin 2) (Fin 6)} {m n : Nat} {a b : Cfg (Fin 2) (Fin 6)}
    (h : ReachesIn M m a b) (hn : m = n) : ReachesIn M n a b := hn ▸ h

macro "countExact" t:term : tactic => `(tactic| (
  refine reindex $t ?_
  first
  | rfl
  | (try simp only [sourceWeightPush, weightNil, weightCons, drBot, drBotZeros, sweep, drOne, drZeros, rnilOne, rnilPow, p1One, p1Pow, p2One, p2Pow]); ring))

macro "countNormList" : tactic => `(tactic|
  simp only [HPow.hPow, List.append_eq,
    blkL, blkR, bumpHead,
    List.replicate_succ, List.replicate_zero, rep0_add_split,
    List.nil_append, List.cons_append, List.append_nil, List.append_assoc,
    rep0_append_zero_cons, List.flatten_cons, List.flatten_nil])


macro "countNormAll" : tactic => `(tactic|
  simp only [decL, decR, decSegs, decLState, decSegs_pushSeg,
    HPow.hPow, List.append_eq,
    blkL, blkR, bumpHead,
    List.replicate_succ, List.replicate_zero, rep0_add_split,
    List.nil_append, List.cons_append, List.append_nil, List.append_assoc,
    rep0_append_zero_cons, List.flatten_cons, List.flatten_nil])


theorem c_rule_BR_zeros_all (L R : List ℕ) (k : ℕ) :
    (cfg_BR target_tm L (rep0 k ++ R)) [target_tm]⊢ᶜ[2*k] (cfg_BR target_tm (rep0 k ++ L) R) := by
  induction k generalizing L with
  | zero => countExact (ReachesIn.zero _ _)
  | succ k ih =>
    have h1 := id (c_rule_BR_zero (target_tm := target_tm) L (rep0 k ++ R))
    have h2 := ih (0 :: L)
    rw [rep0_append_zero_cons k L] at h2
    countExact ReachesIn.trans h1 h2

theorem c_rule_B_zeros_all (L R : List ℕ) (k : ℕ) :
    (cfg_B target_tm L (rep0 k ++ R)) [target_tm]⊢ᶜ[4*k] (cfg_B target_tm (rep0 k ++ L) R) := by
  induction k generalizing L with
  | zero => countExact (ReachesIn.zero _ _)
  | succ k ih =>
    have h1 := id (c_rule_B_zero (target_tm := target_tm) L (rep0 k ++ R))
    have h2 := ih (0 :: L)
    rw [rep0_append_zero_cons k L] at h2
    countExact ReachesIn.trans h1 h2

theorem c_rule_DR0_zeros_all (L R : List ℕ) (k : ℕ) :
    (cfg_DR0 target_tm (rep0 k ++ L) R) [target_tm]⊢ᶜ[4*k] (cfg_DR0 target_tm L (rep0 k ++ R)) := by
  induction k generalizing R with
  | zero => countExact (ReachesIn.zero _ _)
  | succ k ih =>
    have h1 := id (c_rule_DR0_zero (target_tm := target_tm) (rep0 k ++ L) R)
    have h2 := ih (0 :: R)
    rw [rep0_append_zero_cons k R] at h2
    countExact ReachesIn.trans h1 h2

theorem c_rule_B_succ_step (d : ℕ) (L R : List ℕ) :
    (cfg_B target_tm L ((d + 1) :: R)) [target_tm]⊢ᶜ[4] (cfg_BR target_tm (0 :: L) (d :: R)) := by
  countExact ReachesIn.trans (c_rule_B_succ d L R) (c_rule_BR_zero L (d :: R))

theorem c_rule_C_one_prefix (c0 : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (1 :: (rep0 c0 ++ 1 :: L)) R) [target_tm]⊢ᶜ[4*c0+6]
    (cfg_C target_tm (0 :: L) (rep0 c0 ++ 2 :: R)) := by
  cases c0 with
  | zero => countExact id (c_rule_C_one_succ 0 L R)
  | succ n =>
    have h1 := id (c_rule_C_one_zero (target_tm := target_tm) (rep0 n ++ 1 :: L) R)
    have h2 := c_rule_DR0_zeros_all (target_tm := target_tm) (1 :: L) (2 :: R) n
    have h3 := id (c_rule_DR0_succ (target_tm := target_tm) 0 L (rep0 n ++ 2 :: R))
    countExact ReachesIn.trans h1 (ReachesIn.trans h2 h3)

theorem c_rule_C_r_add_three (r : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (rep0 (r + 3) ++ 1 :: L) R) [target_tm]⊢ᶜ[4*r+11]
    (cfg_C target_tm (0 :: L) (blkR r ++ R)) := by
  have heq1 : rep0 (r + 3) ++ 1 :: L = 0 :: 0 :: 0 :: (rep0 r ++ 1 :: L) := by countNormList
  rw [heq1]
  have h1 := id (c_rule_C_zero_zero (target_tm := target_tm) (0 :: (rep0 r ++ 1 :: L))
      R)
  have h2 := c_rule_C_one_prefix (target_tm := target_tm) r L (1 :: R)
  have heq2 : rep0 r ++ 2 :: 1 :: R = blkR r ++ R := by countNormList
  rw [heq2] at h2
  countExact ReachesIn.trans h1 h2

theorem c_rule_C_blkL_pow : ∀ (c r : ℕ) (L R : List ℕ),
    (cfg_C target_tm (0 :: ((blkL r) ^ c ++ L)) R) [target_tm]⊢ᶜ[c*(4*r+11)]
    (cfg_C target_tm (0 :: L) ((blkR r) ^ c ++ R))
  | 0, r, L, R => by simp [drBot, drBotZeros, sweep, drOne, drZeros, rnilOne, rnilPow, p1One, p1Pow, p2One, p2Pow]
  | c + 1, r, L, R => by
    have heq : 0 :: ((blkL r) ^ (c + 1) ++ L) =
        rep0 (r + 3) ++ 1 :: ((blkL r) ^ c ++ L) := by countNormList
    rw [heq]
    have h1 := c_rule_C_r_add_three (target_tm := target_tm) r ((blkL r) ^ c ++ L) R
    have h2 := c_rule_C_blkL_pow c r L (blkR r ++ R)
    have h3 : (blkR r) ^ c ++ (blkR r ++ R) = (blkR r) ^ (c + 1) ++ R := by
      rw [← List.append_assoc, ← pow_succ_right_list]
    rw [h3] at h2
    countExact ReachesIn.trans h1 h2

theorem c_rule_C_bot_four (r : ℕ) (R : List ℕ) :
    (cfg_C target_tm (rep0 (r + 4)) R) [target_tm]⊢ᶜ[4*r+12]
    (cfg_DR0 target_tm [] (blkR r ++ R)) := by
  have heq : rep0 (r + 4) = 0 :: 0 :: 0 :: 0 :: rep0 r := by countNormList
  rw [heq]
  have h1 := id (c_rule_C_zero_zero (target_tm := target_tm) (0 :: 0 :: rep0 r) R)
  have h2 := id (c_rule_C_one_zero (target_tm := target_tm) (rep0 r) (1 :: R))
  have h3 := c_rule_DR0_zeros_all (target_tm := target_tm) [] (2 :: 1 :: R) r
  have heq0 : rep0 r ++ [] = rep0 r := List.append_nil _
  have heq2 : rep0 r ++ 2 :: 1 :: R = blkR r ++ R := by countNormList
  rw [heq0, heq2] at h3
  countExact ReachesIn.trans h1 (ReachesIn.trans h2 h3)

theorem c_rule_DR0_bot (k : ℕ) (R : List ℕ) :
    (cfg_DR0 target_tm (rep0 k) R) [target_tm]⊢ᶜ[drBot k] (cfg_BR target_tm (rep0 (k + 3)) R) := by
  have h0 : rep0 k = rep0 k ++ [] := (List.append_nil _).symm
  rw [h0]
  have h1 := c_rule_DR0_zeros_all (target_tm := target_tm) [] R k
  have h2 := id (c_rule_DR0_nil (target_tm := target_tm) (rep0 k ++ R))
  have h3 := id (c_rule_C_one_nil (target_tm := target_tm) (rep0 k ++ R))
  have h4 := id (c_rule_B_succ_step (target_tm := target_tm) 0 [0] (rep0 k ++ R))
  have h5 := c_rule_BR_zeros_all (target_tm := target_tm) [0, 0] R (k + 1)
  have heqR : 0 :: (rep0 k ++ R) = rep0 (k + 1) ++ R := rfl
  have heqL : rep0 (k + 1) ++ [0, 0] = rep0 (k + 3) := by countNormList
  rw [heqR] at h4; rw [heqL] at h5
  countExact ReachesIn.trans h1 (ReachesIn.trans h2 (ReachesIn.trans h3 (ReachesIn.trans h4 h5)))

theorem c_rule_DR0_bot_zeros : ∀ (q k : ℕ) (R : List ℕ),
    (cfg_DR0 target_tm (rep0 k) (1 :: (rep0 q ++ R))) [target_tm]⊢ᶜ[drBotZeros q k]
    (cfg_DR0 target_tm (rep0 (k + 3 * q)) (1 :: R))
  | 0, k, R => by simp [drBot, drBotZeros, sweep, drOne, drZeros, rnilOne, rnilPow, p1One, p1Pow, p2One, p2Pow]
  | q + 1, k, R => by
    have h1 := c_rule_DR0_bot (target_tm := target_tm) k (1 :: (0 :: (rep0 q ++ R)))
    have h2 := id (c_rule_BR_one (target_tm := target_tm) (rep0 (k + 3))
        (0 :: (rep0 q ++ R)))
    have h3 := c_rule_DR0_bot_zeros q (k + 3) R
    have heq : k + 3 + 3 * q = k + 3 * (q + 1) := by omega
    rw [heq] at h3
    countExact ReachesIn.trans h1 (ReachesIn.trans h2 h3)

theorem c_rule_BR_blkR_one (r : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm (0 :: L) (blkR r ++ R)) [target_tm]⊢ᶜ[2*r+15]
    (cfg_BR target_tm (rep0 3 ++ 1 :: (rep0 r ++ L)) R) := by
  have h0 : blkR r ++ R = rep0 r ++ (2 :: 1 :: R) := by countNormList
  rw [h0]
  have h1 := c_rule_BR_zeros_all (target_tm := target_tm) (0 :: L) (2 :: 1 :: R) r
  rw [rep0_append_zero_cons r L] at h1
  have h2 := id (c_rule_BR_add_two (target_tm := target_tm) 0
      (0 :: (rep0 r ++ L)) (1 :: R))
  have h3 := id (c_rule_B_zero (target_tm := target_tm) (1 :: (rep0 r ++ L)) (1 :: R))
  have h4 := id (c_rule_B_succ_step (target_tm := target_tm) 0
      (0 :: 1 :: (rep0 r ++ L)) R)
  have h5 := id (c_rule_BR_zero (target_tm := target_tm)
      (0 :: 0 :: 1 :: (rep0 r ++ L)) R)
  countExact ReachesIn.trans h1 (ReachesIn.trans h2 (ReachesIn.trans h3 (ReachesIn.trans h4 h5)))

theorem c_rule_BR_blkR_succ : ∀ (k r : ℕ) (L R : List ℕ),
    (cfg_BR target_tm (0 :: L) ((blkR r) ^ (k + 1) ++ R)) [target_tm]⊢ᶜ[(k+1)*(2*r+15)]
    (cfg_BR target_tm (rep0 3 ++ 1 :: ((blkL r) ^ k ++ (rep0 r ++ L))) R)
  | 0, r, L, R => by
    simpa [HPow.hPow, List.append_eq, List.replicate_succ, List.replicate_zero, List.flatten_cons
        , List.flatten_nil] using c_rule_BR_blkR_one r L R
  | k + 1, r, L, R => by
    have heqR : (blkR r) ^ (k + 2) ++ R = blkR r ++ ((blkR r) ^ (k + 1) ++ R) := by
      simp [HPow.hPow, List.replicate_succ, List.flatten_cons, List.append_assoc]
    rw [heqR]
    have h1 := c_rule_BR_blkR_one (target_tm := target_tm) r L ((blkR r) ^ (k + 1) ++ R)
    have h2 := c_rule_BR_blkR_succ k r (0 :: 0 :: 1 :: (rep0 r ++ L)) R
    have heqL1 : rep0 3 ++ 1 :: (rep0 r ++ L) = 0 :: (0 :: 0 :: 1 :: (rep0 r ++ L)) := rfl
    rw [heqL1] at h1
    have heqL2 : (blkL r) ^ k ++ (rep0 r ++ (0 :: 0 :: 1 :: (rep0 r ++ L))) =
        (blkL r) ^ (k + 1) ++ (rep0 r ++ L) := by
      have hb : rep0 r ++ (0 :: 0 :: 1 :: (rep0 r ++ L)) = blkL r ++ (rep0 r ++ L) := by countNormList
      rw [hb, ← List.append_assoc, ← pow_succ_right_list]
    rw [heqL2] at h2
    countExact ReachesIn.trans h1 h2

theorem c_rule_BR_blkR_clean (c r : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm (rep0 3 ++ 1 :: L) ((blkR r) ^ c ++ R)) [target_tm]⊢ᶜ[c*(2*r+15)]
    (cfg_BR target_tm (rep0 3 ++ 1 :: ((blkL r) ^ c ++ L)) R) := by
  cases c with
  | zero => countExact (ReachesIn.zero _ _)
  | succ k =>
    have h := c_rule_BR_blkR_succ (target_tm := target_tm) k r (0 :: 0 :: 1 :: L) R
    have heq1 : (blkL r) ^ k ++ (rep0 r ++ (0 :: 0 :: 1 :: L)) =
        (blkL r) ^ (k + 1) ++ L := by
      have hb : rep0 r ++ (0 :: 0 :: 1 :: L) = blkL r ++ L := by countNormList
      rw [hb, ← List.append_assoc, ← pow_succ_right_list]
    rw [heq1] at h
    countExact h

theorem c_clean_sweep_core : ∀ (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_C target_tm (0 :: (decSegs segs ++ rep0 (bot + 3))) R) [target_tm]⊢ᶜ[sweep bot (weight segs)]
    (cfg_BR target_tm (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) R)
  | [], bot, R => by
    dsimp only [decSegs]
    have heq : (0 :: ([] ++ rep0 (bot + 3))) = rep0 (bot + 4) := by countNormAll
    rw [heq]
    have h1 := c_rule_C_bot_four (target_tm := target_tm) bot R
    have h2 := c_rule_DR0_bot (target_tm := target_tm) 0 (blkR bot ++ R)
    have h3 := c_rule_BR_blkR_one (target_tm := target_tm) bot [0, 0] R
    have heq2 : rep0 bot ++ [0, 0] = rep0 (bot + 2) := by countNormAll
    rw [heq2] at h3
    countExact ReachesIn.trans h1 (ReachesIn.trans h2 h3)
  | (r, c) :: ss, bot, R => by
    dsimp only [decSegs]
    rw [List.append_assoc]
    have h1 := c_rule_C_blkL_pow (target_tm := target_tm) c r (decSegs ss ++ rep0 (bot + 3)) R
    have h2 := c_clean_sweep_core ss bot ((blkR r) ^ c ++ R)
    have h3 := c_rule_BR_blkR_clean (target_tm := target_tm) c r (decSegs ss ++ rep0 (bot + 2)) R
    rw [← List.append_assoc] at h3
    countExact ReachesIn.trans h1 (ReachesIn.trans h2 h3)

theorem c_clean_DR0_one (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ) :
    (cfg_DR0 target_tm (decLState (.clean c0 segs (bot + 1))) R) [target_tm]⊢ᶜ[drOne c0 bot (weight segs)]
    (cfg_BR target_tm (decLState (.clean (c0 + 4) segs bot)) R) := by
  dsimp only [decLState]
  have h1 := c_rule_DR0_zeros_all (target_tm := target_tm)
      (1 :: (decSegs segs ++ rep0 (bot + 3))) R c0
  have h2 := id (c_rule_DR0_succ (target_tm := target_tm) 0
      (decSegs segs ++ rep0 (bot + 3)) (rep0 c0 ++ R))
  have h3 := c_clean_sweep_core (target_tm := target_tm) segs bot (0 :: (rep0 c0 ++ R))
  have h4 := c_rule_BR_zeros_all (target_tm := target_tm)
      (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) R (c0 + 1)
  have heqL : rep0 (c0 + 1) ++ (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
      rep0 (c0 + 4) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)) := by countNormAll
  rw [heqL] at h4
  countExact ReachesIn.trans h1 (ReachesIn.trans h2 (ReachesIn.trans h3 h4))

theorem c_clean_DR0_zeros : ∀ (q c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_DR0 target_tm (decLState (.clean c0 segs (bot + q))) (1 :: (rep0 q ++ R))) [target_tm]⊢ᶜ[drZeros q c0 bot (weight segs)]
    (cfg_DR0 target_tm (decLState (.clean (c0 + 4 * q) segs bot)) (1 :: R))
  | 0, c0, segs, bot, R => by simp [drBot, drBotZeros, sweep, drOne, drZeros, rnilOne, rnilPow, p1One, p1Pow, p2One, p2Pow]
  | q + 1, c0, segs, bot, R => by
    rw [show bot + (q + 1) = (bot + q) + 1 by omega]
    have h1 := c_clean_DR0_one (target_tm := target_tm) c0 segs (bot + q) (1 :: (0 :: (rep0 q ++ R)))
    have h2 := id (c_rule_BR_one (target_tm := target_tm)
        (decLState (.clean (c0 + 4) segs (bot + q))) (0 :: (rep0 q ++ R)))
    have h3 := c_clean_DR0_zeros q (c0 + 4) segs bot R
    have heq : c0 + 4 + 4 * q = c0 + 4 * (q + 1) := by omega
    rw [heq] at h3
    countExact ReachesIn.trans h1 (ReachesIn.trans h2 h3)

theorem c_clean_RNIL_one (m : StackMode) (hm : m = .B ∨ m = .BR)
    (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) :
    (evalStackCfg1 target_tm m (decLState (.clean (c0 + 1) segs (bot + 1))) []) [target_tm]⊢ᶜ[rnilOne c0 bot (weight segs)]
    (cfg_B target_tm (decLState (.clean 1 (pushSeg c0 1 segs) bot)) []) := by
  have h0 : (evalStackCfg1 target_tm m (decLState (.clean (c0 + 1) segs (bot + 1))) [])
      [target_tm]⊢ᶜ[1]
      (cfg_C target_tm (1 :: (rep0 c0 ++ 1 :: (decSegs segs ++ rep0 (bot + 3)))) []) := by
    have heqL : bumpHead (decLState (.clean (c0 + 1) segs (bot + 1))) =
        1 :: (rep0 c0 ++ 1 :: (decSegs segs ++ rep0 (bot + 3))) := by countNormAll
    rcases hm with rfl | rfl
    · rw [← heqL]; countExact id (c_rule_B_nil _)
    · rw [← heqL]; countExact id (c_rule_BR_nil _)
  have h1 := c_rule_C_one_prefix (target_tm := target_tm) c0 (decSegs segs ++ rep0 (bot + 3)) []
  have h2 := c_clean_sweep_core (target_tm := target_tm) segs bot (rep0 c0 ++ [2])
  have h3 := c_rule_BR_zeros_all (target_tm := target_tm)
      (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) [2] c0
  have heq3 : rep0 c0 ++ (rep0 3 ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
      0 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) := by countNormAll
  rw [heq3] at h3
  have h4 := id (c_rule_BR_add_two (target_tm := target_tm) 0
      (0 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))) [])
  have h5 := id (c_rule_B_zero (target_tm := target_tm)
      (1 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2)))) [])
  have heq5 : 0 :: 1 :: (rep0 (c0 + 2) ++ 1 :: (decSegs segs ++ rep0 (bot + 2))) =
      decLState (.clean 1 (pushSeg c0 1 segs) bot) := by countNormAll
  rw [heq5] at h5
  countExact ReachesIn.trans h0 (ReachesIn.trans h1 (ReachesIn.trans h2 (ReachesIn.trans h3 (ReachesIn.trans
      h4 h5))))

theorem c_clean_RNIL_zero_pow : ∀ (q : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ),
    (cfg_B target_tm (decLState (.clean 1 segs (bot + q))) []) [target_tm]⊢ᶜ[rnilPow q bot (weight segs)]
    (cfg_B target_tm (decLState (.clean 1 (pushSeg 0 q segs) bot)) [])
  | 0, segs, bot => by simp [drBot, drBotZeros, sweep, drOne, drZeros, rnilOne, rnilPow, p1One, p1Pow, p2One, p2Pow, pushSeg]
  | q + 1, segs, bot => by
    rw [show bot + (q + 1) = (bot + q) + 1 by omega]
    have h1 := c_clean_RNIL_one (target_tm := target_tm) .B (Or.inl rfl) 0 segs (bot + q)
    have h2 := c_clean_RNIL_zero_pow q (pushSeg 0 1 segs) bot
    have heqL : decLState (.clean 1 (pushSeg 0 q (pushSeg 0 1 segs)) bot) =
        decLState (.clean 1 (pushSeg 0 (q + 1) segs) bot) := by
      simp [decLState, decSegs_pushSeg_succ]
    rw [heqL] at h2
    countExact ReachesIn.trans h1 h2

theorem c_clean_P1_one (r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ) :
    (cfg_B target_tm (decLState (.clean 0 segs (bot + 1))) (0 :: (blkR r ++ R))) [target_tm]⊢ᶜ[p1One r bot (weight segs)]
    (cfg_B target_tm (decLState (.clean 0 (pushSeg (r + 3) 1 segs) bot)) (0 :: R)) := by
  have heqR : 0 :: (blkR r ++ R) = rep0 (r + 1) ++ (2 :: 1 :: R) := by countNormAll
  rw [heqR]
  have h1 := c_rule_B_zeros_all (target_tm := target_tm)
      (decLState (.clean 0 segs (bot + 1))) (2 :: 1 :: R) (r + 1)
  have h2 := id (c_rule_B_succ_step (target_tm := target_tm) 1
      (rep0 (r + 1) ++ decLState (.clean 0 segs (bot + 1))) (1 :: R))
  have heq2 : 0 :: (rep0 (r + 1) ++ decLState (.clean 0 segs (bot + 1))) =
      decLState (.clean (r + 2) segs (bot + 1)) := by countNormAll
  rw [heq2] at h2
  have h3 := id (c_rule_BR_one (target_tm := target_tm)
      (decLState (.clean (r + 2) segs (bot + 1))) (1 :: R))
  have h4 := c_clean_DR0_one (target_tm := target_tm) (r + 2) segs bot (2 :: R)
  have h5 := id (c_rule_BR_add_two (target_tm := target_tm) 0
      (decLState (.clean (r + 6) segs bot)) R)
  have heq5 : bumpHead (decLState (.clean (r + 6) segs bot)) =
      decLState (.clean 0 (pushSeg (r + 3) 1 segs) bot) := by countNormAll
  rw [heq5] at h5
  countExact ReachesIn.trans h1 (ReachesIn.trans h2 (ReachesIn.trans h3 (ReachesIn.trans h4 h5)))

theorem c_clean_P1_pow : ∀ (q r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_B target_tm (decLState (.clean 0 segs (bot + q))) (0 :: ((blkR r) ^ q ++ R)))
        [target_tm]⊢ᶜ[p1Pow q r bot (weight segs)]
    (cfg_B target_tm (decLState (.clean 0 (pushSeg (r + 3) q segs) bot)) (0 :: R))
  | 0, r, segs, bot, R => by simp [drBot, drBotZeros, sweep, drOne, drZeros, rnilOne, rnilPow, p1One, p1Pow, p2One, p2Pow, pushSeg, HPow.hPow, List.flatten_nil]
  | q + 1, r, segs, bot, R => by
    rw [show bot + (q + 1) = (bot + q) + 1 by omega]
    have heqR : (blkR r) ^ (q + 1) ++ R = blkR r ++ ((blkR r) ^ q ++ R) := by
      simp [HPow.hPow, List.replicate_succ, List.flatten_cons, List.append_assoc]
    rw [heqR]
    have h1 := c_clean_P1_one (target_tm := target_tm) r segs (bot + q) ((blkR r) ^ q ++ R)
    have h2 := c_clean_P1_pow q r (pushSeg (r + 3) 1 segs) bot R
    have heqL : decLState (.clean 0 (pushSeg (r + 3) q (pushSeg (r + 3) 1 segs)) bot) =
        decLState (.clean 0 (pushSeg (r + 3) (q + 1) segs) bot) := by
      simp [decLState, decSegs_pushSeg_succ]
    rw [heqL] at h2
    countExact ReachesIn.trans h1 h2

theorem c_clean_P2_one (r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ) :
    (cfg_B target_tm (decLState (.clean 0 segs (bot + (r + 1)))) (1 :: 1 :: (blkR r ++ R)))
        [target_tm]⊢ᶜ[p2One r bot (weight segs)]
    (cfg_B target_tm (decLState (.clean 0 (pushSeg (4 * r + 3) 1 segs) bot)) (1 :: 1 :: R)) := by
  cases r with
  | zero =>
    have h1 := id (c_rule_B_succ_step (target_tm := target_tm) 0
        (decLState (.clean 0 segs (bot + 1))) (1 :: (blkR 0 ++ R)))
    have h2 := id (c_rule_BR_zero (target_tm := target_tm)
        (0 :: decLState (.clean 0 segs (bot + 1))) (1 :: (blkR 0 ++ R)))
    have heq2 : 0 :: 0 :: decLState (.clean 0 segs (bot + 1)) =
        decLState (.clean 2 segs (bot + 1)) := rfl
    rw [heq2] at h2
    have h3 := id (c_rule_BR_one (target_tm := target_tm)
        (decLState (.clean 2 segs (bot + 1))) (blkR 0 ++ R))
    have hb0 : bumpHead (blkR 0 ++ R) = 3 :: 1 :: R := rfl
    rw [hb0] at h3
    have h4 := c_clean_DR0_one (target_tm := target_tm) 2 segs bot (3 :: 1 :: R)
    have h5 := id (c_rule_BR_add_two (target_tm := target_tm) 1
        (decLState (.clean 6 segs bot)) (1 :: R))
    have heq5 : bumpHead (decLState (.clean 6 segs bot)) =
        decLState (.clean 0 (pushSeg 3 1 segs) bot) := by countNormAll
    rw [heq5] at h5
    countExact ReachesIn.trans h1 (ReachesIn.trans h2 (ReachesIn.trans h3 (ReachesIn.trans h4 h5)))
  | succ r' =>
    rw [show bot + (r' + 1 + 1) = (bot + 2) + r' by omega]
    have h1 := id (c_rule_B_succ_step (target_tm := target_tm) 0
        (decLState (.clean 0 segs ((bot + 2) + r'))) (1 :: (blkR (r' + 1) ++ R)))
    have h2 := id (c_rule_BR_zero (target_tm := target_tm)
        (0 :: decLState (.clean 0 segs ((bot + 2) + r'))) (1 :: (blkR (r' + 1) ++ R)))
    have heq2 : 0 :: 0 :: decLState (.clean 0 segs ((bot + 2) + r')) =
        decLState (.clean 2 segs ((bot + 2) + r')) := rfl
    rw [heq2] at h2
    have h3 := id (c_rule_BR_one (target_tm := target_tm)
        (decLState (.clean 2 segs ((bot + 2) + r'))) (blkR (r' + 1) ++ R))
    have hb : bumpHead (blkR (r' + 1) ++ R) = 1 :: (rep0 r' ++ (2 :: 1 :: R)) := by countNormAll
    rw [hb] at h3
    have h4 := c_clean_DR0_zeros (target_tm := target_tm) r' 2 segs (bot + 2) (2 :: 1 :: R)
    have h5 := c_clean_DR0_one (target_tm := target_tm) (2 + 4 * r') segs (bot + 1) (1 :: 2 :: 1 :: R)
    have h6 := id (c_rule_BR_one (target_tm := target_tm)
        (decLState (.clean (2 + 4 * r' + 4) segs (bot + 1))) (2 :: 1 :: R))
    have h7 := c_clean_DR0_one (target_tm := target_tm) (2 + 4 * r' + 4) segs bot (3 :: 1 :: R)
    have h8 := id (c_rule_BR_add_two (target_tm := target_tm) 1
        (decLState (.clean (2 + 4 * r' + 8) segs bot)) (1 :: R))
    have heq8 : bumpHead (decLState (.clean (2 + 4 * r' + 8) segs bot)) =
        decLState (.clean 0 (pushSeg (4 * (r' + 1) + 3) 1 segs) bot) := by
      rw [show 4 * (r' + 1) + 3 = 4 * r' + 7 by omega]
      countNormAll
    rw [heq8] at h8
    countExact ReachesIn.trans h1 (ReachesIn.trans h2 (ReachesIn.trans h3
      (ReachesIn.trans h4 (ReachesIn.trans h5 (ReachesIn.trans h6 (ReachesIn.trans h7 h8))))))

theorem c_clean_P2_pow : ∀ (q r : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List ℕ),
    (cfg_B target_tm (decLState (.clean 0 segs (bot + q * (r + 1)))) (1 :: 1 :: ((blkR r) ^ q ++
        R))) [target_tm]⊢ᶜ[p2Pow q r bot (weight segs)]
    (cfg_B target_tm (decLState (.clean 0 (pushSeg (4 * r + 3) q segs) bot)) (1 :: 1 :: R))
  | 0, r, segs, bot, R => by simp [drBot, drBotZeros, sweep, drOne, drZeros, rnilOne, rnilPow, p1One, p1Pow, p2One, p2Pow, pushSeg, HPow.hPow, List.flatten_nil]
  | q + 1, r, segs, bot, R => by
    rw [show bot + (q + 1) * (r + 1) = (bot + q * (r + 1)) + (r + 1) by
      rw [Nat.succ_mul, Nat.add_assoc]]
    have heqR : (blkR r) ^ (q + 1) ++ R = blkR r ++ ((blkR r) ^ q ++ R) := by
      simp [HPow.hPow, List.replicate_succ, List.flatten_cons, List.append_assoc]
    rw [heqR]
    have h1 := c_clean_P2_one (target_tm := target_tm) r segs (bot + q * (r + 1))
        ((blkR r) ^ q ++ R)
    have h2 := c_clean_P2_pow q r (pushSeg (4 * r + 3) 1 segs) bot R
    have heqL : decLState (.clean 0 (pushSeg (4 * r + 3) q (pushSeg (4 * r + 3) 1 segs)) bot) =
        decLState (.clean 0 (pushSeg (4 * r + 3) (q + 1) segs) bot) := by
      simp [decLState, decSegs_pushSeg_succ]
    rw [heqL] at h2
    countExact ReachesIn.trans h1 h2

end BB6.Agent17.RleCounted

#print axioms BB6.Agent17.RleCounted.c_rule_BR_zeros_all
#print axioms BB6.Agent17.RleCounted.c_rule_B_zeros_all
#print axioms BB6.Agent17.RleCounted.c_rule_DR0_zeros_all
#print axioms BB6.Agent17.RleCounted.c_rule_B_succ_step
#print axioms BB6.Agent17.RleCounted.c_rule_C_one_prefix
#print axioms BB6.Agent17.RleCounted.c_rule_C_r_add_three
#print axioms BB6.Agent17.RleCounted.c_rule_C_blkL_pow
#print axioms BB6.Agent17.RleCounted.c_rule_C_bot_four
#print axioms BB6.Agent17.RleCounted.c_rule_DR0_bot
#print axioms BB6.Agent17.RleCounted.c_rule_DR0_bot_zeros
#print axioms BB6.Agent17.RleCounted.c_rule_BR_blkR_one
#print axioms BB6.Agent17.RleCounted.c_rule_BR_blkR_succ
#print axioms BB6.Agent17.RleCounted.c_rule_BR_blkR_clean
#print axioms BB6.Agent17.RleCounted.c_clean_sweep_core
#print axioms BB6.Agent17.RleCounted.c_clean_DR0_one
#print axioms BB6.Agent17.RleCounted.c_clean_DR0_zeros
#print axioms BB6.Agent17.RleCounted.c_clean_RNIL_one
#print axioms BB6.Agent17.RleCounted.c_clean_RNIL_zero_pow
#print axioms BB6.Agent17.RleCounted.c_clean_P1_one
#print axioms BB6.Agent17.RleCounted.c_clean_P1_pow
#print axioms BB6.Agent17.RleCounted.c_clean_P2_one
#print axioms BB6.Agent17.RleCounted.c_clean_P2_pow




open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RleStackEngine
open BB6.Agent17.RleCost (weight drBot drBotZeros sweep drOne drZeros rnilOne rnilPow p1One p1Pow p2One p2Pow)
namespace BB6.Agent17.RleCounted

-- Exact charge for the same branch of each executable RLE operation.
def costRawB (items R : List Item) : Nat :=
  match R with
  | [] => 1
  | .z c :: _ => 4*c
  | _ =>
    match popR1 R with
    | none => 1
    | some (d, _) => if Nat.beq d 0 then 4 else 2

def costRawBRPop (items R : List Item) : Nat :=
  match popR1 R with
  | none => 1
  | some (d, _) => if Nat.beq d 0 then 2 else if Nat.beq d 1 then 4 else 5

def costRawBR (items R : List Item) : Nat :=
  match R with
  | [] => 1
  | .z c :: _ => 2*c
  | .k r m :: R1 =>
    if Nat.ble 1 m then
      match popL1 items with
      | some (a, _) => if Nat.beq a 0 then m*(2*r+15) else costRawBRPop items (.k r m :: R1)
      | none => costRawBRPop items (.k r m :: R1)
    else 0
  | .d v :: R1 => costRawBRPop items (.d v :: R1)

def costRawDR0Atomic (items R : List Item) : Nat :=
  match popL1 items with
  | none => 3
  | some (a, _) =>
    if Nat.beq a 0 then
      match items with
      | .z c :: _ => 4*c
      | _ => 4
    else 3

def costRawDR0 (items R : List Item) : Nat :=
  match items with
  | [.z c] =>
    match R with
    | .d v1 :: .z q :: _ => if Nat.beq v1 1 then drBotZeros q c else drBot c
    | _ => drBot c
  | _ => costRawDR0Atomic items R

def costRawCAtomic (items R : List Item) : Nat :=
  match popL1 items with
  | none => 1
  | some (a, L1) =>
    if Nat.beq a 0 then
      match popL1 L1 with
      | none => 3
      | some (a1, _) => if Nat.beq a1 0 then 5 else if Nat.beq a1 1 then 17 else 4
    else if Nat.beq a 1 then
      match popL1 L1 with
      | none => 5
      | some (a1, _) => if Nat.beq a1 0 then 7 else 6
    else 3

def costRawC (items R : List Item) : Nat :=
  match items with
  | .z cz :: .k r m :: _ =>
    if Nat.beq cz 1 then m*(4*r+11) else costRawCAtomic items R
  | .z cz :: .d v1 :: _ =>
    if Nat.ble 4 cz && Nat.beq v1 1 then 4*(cz-3)+11 else costRawCAtomic items R
  | [.z cz] =>
    if Nat.ble 4 cz then 4*(cz-4)+12 else costRawCAtomic items R
  | _ => costRawCAtomic items R

def costCleanBPop (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) (R : List Item) : Nat :=
  match popR1 R with
  | none => 0
  | some (d, _) => if Nat.beq d 0 then 4 else 2

def costRNIL (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) : Nat :=
  rnilOne (c0-1) (bot-1) (weight segs) +
    rnilPow (bot-1) 0 (weight (pushSeg (c0-1) 1 segs))

def costCleanB (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) (R : List Item) : Nat :=
  match R with
  | [] =>
    if Nat.ble 1 c0 && Nat.ble 1 bot then costRNIL c0 segs bot else 0
  | .z cz :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.ble 1 bot && Nat.beq cz 1 then
      let q := minNat cnt bot
      if Nat.ble 1 q then p1Pow q r (bot-q) (weight segs) else 4*cz
    else 4*cz
  | .z cz :: _ => 4*cz
  | .d v1 :: .d v2 :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.beq v1 1 && Nat.beq v2 1 then
      let q := minNat cnt (bot / (r+1))
      if Nat.ble 1 q then p2Pow q r (bot-q*(r+1)) (weight segs) else 2
    else costCleanBPop c0 segs bot (.d v1 :: .d v2 :: .k r cnt :: Rrem)
  | _ => costCleanBPop c0 segs bot R

def costCleanBR (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) (R : List Item) : Nat :=
  match R with
  | [] => if Nat.ble 1 c0 && Nat.ble 1 bot then costRNIL c0 segs bot else 0
  | .z cz :: _ => 2*cz
  | .k r m :: _ =>
    if Nat.ble 1 m && Nat.ble 1 c0 && Nat.ble 3 (r+c0) then m*(2*r+15) else 0
  | .d v :: R1 =>
    match popR1 (.d v :: R1) with
    | none => 0
    | some (d, _) =>
      if Nat.beq d 0 then 2 else if Nat.beq d 1 then 4 else if Nat.ble 3 c0 then 5 else 0

def costCleanDR0 (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) (R : List Item) : Nat :=
  if Nat.ble 1 bot then
    match R with
    | .d v1 :: .z rz :: _ =>
      if Nat.beq v1 1 then
        let q := minNat rz bot
        if Nat.ble 1 q then drZeros q c0 (bot-q) (weight segs)
        else drOne c0 (bot-1) (weight segs)
      else drOne c0 (bot-1) (weight segs)
    | _ => drOne c0 (bot-1) (weight segs)
  else 0

def costRleStep (s : RleFullState) : Nat :=
  match s.ls with
  | .raw items =>
    match tryPack s.mode items s.R with
    | some _ => 0
    | none =>
      match s.mode with
      | .B => costRawB items s.R
      | .BR => costRawBR items s.R
      | .DR0 => costRawDR0 items s.R
      | .C => costRawC items s.R
  | .clean c0 segs bot =>
    match s.mode with
    | .B => costCleanB c0 segs bot s.R
    | .BR => costCleanBR c0 segs bot s.R
    | .DR0 => costCleanDR0 c0 segs bot s.R
    | .C => 0

end BB6.Agent17.RleCounted


/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in upstream LICENSE.
Count-indexed variants of original dispatcher proofs at 3647718b5df22e1a61462dec0376bd204526285a.
Source-import compilation required before use as a proof.
-/


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
        countPrep
        simpa [evalRle, evalStackCfg1, decLState] using c_stepRawB_halts items R n hh
      | BR => 
        countPrep
        simpa [evalRle, evalStackCfg1, decLState] using c_stepRawBR_halts items R n hh
      | DR0 => 
        countPrep
        simpa [evalRle, evalStackCfg1, decLState] using c_stepRawDR0_halts items R n hh
      | C => 
        countPrep
        simpa [evalRle, evalStackCfg1, decLState] using c_stepRawC_halts items R n hh
  | clean c0 segs bot =>
    dsimp only at hh
    cases mode with
    | B => 
        countPrep
        simpa [evalRle, evalStackCfg1, decLState] using c_stepCleanB_halts c0 segs bot R n hh
    | BR => 
        countPrep
        simpa [evalRle, evalStackCfg1, decLState] using c_stepCleanBR_halts c0 segs bot R n hh
    | DR0 => 
        countPrep
        simpa [evalRle, evalStackCfg1, decLState] using c_stepCleanDR0_halts c0 segs bot R n hh
    | C =>
      countTransfer hh
      simp [evalRle, evalStackCfg1, decLState, decL_unpackClean]

end BB6.Agent17.RleCounted

#print axioms BB6.Agent17.RleCounted.c_rleStep_halts


/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in upstream LICENSE.
Checkpoint data and state equalities from cryptids at 3647718b5df22e1a61462dec0376bd204526285a.
Exact indexed cost composition and cost equations added here.
-/

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RleStackEngine
namespace BB6.Agent17.RleCounted

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

def costStepsInner (n : Nat) (s : RleFullState) : Nat :=
  Nat.rec (fun _ => 0)
    (fun _ ih s =>
      match s with
      | ⟨_, _, _, true⟩ => 0
      | ⟨m, ls, R, false⟩ =>
        strictNat (costRleStep ⟨m, ls, R, false⟩) (fun c =>
          strictStateFast (rleStep ⟨m, ls, R, false⟩) (fun s' => c + ih s')))
    n s

theorem costStepsInner_succ (n : Nat) (s : RleFullState) :
    costStepsInner (n+1) s =
      match s with
      | ⟨_, _, _, true⟩ => 0
      | ⟨m, ls, R, false⟩ =>
        strictNat (costRleStep ⟨m, ls, R, false⟩) (fun c =>
          strictStateFast (rleStep ⟨m, ls, R, false⟩) (fun s' => c + costStepsInner n s')) := rfl

def costBatches (b : Nat) (s : RleFullState) : Nat :=
  Nat.rec (fun _ => 0)
    (fun _ ih s => strictNat (costStepsInner 25 s) (fun c =>
      strictState (runStepsInner 25 s) (fun s' => c + ih s')))
    b s

theorem costBatches_succ (b : Nat) (s : RleFullState) :
    costBatches (b+1) s =
      strictNat (costStepsInner 25 s) (fun c =>
        strictState (runStepsInner 25 s) (fun s' => c + costBatches b s')) := rfl

variable {target_tm : Machine (Fin 2) (Fin 6)} [CountedRules target_tm]

theorem costStepsInner_halts : ∀ (steps : Nat) (s : RleFullState) (n : Nat),
    StateHaltsAt target_tm (runStepsInner steps s) n →
    StateHaltsAt target_tm s (costStepsInner steps s + n)
  | 0, s, n, h => by simpa [costStepsInner, runStepsInner] using h
  | steps+1, ⟨m, ls, R, true⟩, n, h => by
    rw [runStepsInner_succ] at h
    rw [costStepsInner_succ]
    simpa using h
  | steps+1, ⟨m, ls, R, false⟩, n, h => by
    rw [runStepsInner_succ] at h
    dsimp only at h
    rw [strictStateFast_eq] at h
    have hh := costStepsInner_halts steps (rleStep ⟨m,ls,R,false⟩) n h
    have hh' := c_rleStep_halts ⟨m,ls,R,false⟩ _ hh
    rw [costStepsInner_succ]
    dsimp only
    rw [strictNat_eq, strictStateFast_eq, Nat.add_assoc]
    exact hh'

theorem costBatches_halts : ∀ (b : Nat) (s : RleFullState) (n : Nat),
    StateHaltsAt target_tm (runBatches b s) n →
    StateHaltsAt target_tm s (costBatches b s + n)
  | 0, s, n, h => by simpa [costBatches, runBatches] using h
  | b+1, s, n, h => by
    rw [runBatches_succ, strictState_eq] at h
    have h2 := costBatches_halts b (runStepsInner 25 s) n h
    have h3 := costStepsInner_halts 25 s _ h2
    rw [costBatches_succ, strictNat_eq, strictState_eq, Nat.add_assoc]
    exact h3

theorem counted_chunk_back {b k n : Nat} {s1 s2 : RleFullState}
    (heq : runBatches b s1 = s2) (hc : costBatches b s1 = k)
    (h : StateHaltsAt target_tm s2 n) :
    StateHaltsAt target_tm s1 (k+n) := by
  rw [← heq] at h
  have hh := costBatches_halts b s1 n h
  rw [hc] at hh
  exact hh

theorem counted_final_chunk {b k : Nat} {s : RleFullState}
    (hf : (runBatches b s).halted = true) (hc : costBatches b s = k) :
    StateHaltsAt target_tm s k := by
  have h : StateHaltsAt target_tm (runBatches b s) 0 := by
    simp [StateHaltsAt, hf]
  have hh := costBatches_halts b s 0 h
  rw [hc, Nat.add_zero] at hh
  exact hh


namespace First

def ckpt0 : RleFullState := ⟨.B, .raw [.z 1], [], false⟩

def ckpt5 : RleFullState := ⟨.B, .clean 0 [(10160322, 1), (2037954, 13), (2824386, 1619), (3086530
    , 1), (3610818, 3653), (2037954, 1), (25368770, 1), (42145986, 2872), (58923202, 1), (92477634
    , 812), (12785858, 1), (1275271362, 28), (3666548930, 1), (5101263042, 71), (15178199234, 1),
    (20405054658, 116), (25977842882, 1), (81620331714, 22), (248318268209, 1), (300302521103, 1)]
    3842700283260, [.z 1, .k 8126655 6, .k 2031599 1, .k 2031615 34318, .k 1507327 1, .k 1245183
    24417, .k 2031615 1, .k 458751 473610, .k 196607 1, .k 65535 2829536, .k 3071 1, .k 7167
    3190216, .k 3071 1, .k 1023 323903800, .k 511 1, .k 255 4583538500, .k 127 1, .k 63
    26276947360, .k 31 1, .k 15 56657308304, .z 3, .d 1, .z 2, .d 2, .d 1, .k 3 133852318911, .z 3
    , .d 3, .d 1, .k 0 56344583818, .d 2], false⟩

def ckpt10 : RleFullState := ⟨.C, .raw [.z 1, .k 20401242237 24417, .k 24696209533 1, .k
    33286144125 34307, .k 41607680637 1, .k 8321537661 9, .k 8321472125 1, .k 33286821501 6, .k
    41616709245 1, .k 8347489917 13, .k 11568715389 1619, .k 12642457213 1, .k 14789940861 3653,
    .k 8347489917 1, .k 103910512253 1, .k 172629988989 2872, .k 241349465725 1, .k 378788419197
    812, .k 52370904701 1, .k 5223511529085 28, .k 15018184447613 1, .k 20894773450365 71, .k
    62169904092797 1, .k 83579103909501 27, .k 233893724569877 1, .k 334316415637929 88, .k
    425620977899945 1, .k 1337267514923433 4, .k 110188252487541 1, .k 19633268198974271 1, .z 2]
    , [.k 33286144125 1, .k 7516340349 473610, .k 3221373053 1, .k 1073889405 2829536, .k 50479229
    1, .k 117588093 3190216, .k 50479229 1, .k 16924797 323903800, .k 8536189 1, .k 4341885
    1304636057, .k 1720010 1, .k 1085472 3278902442, .k 561184 1, .k 299040 16080887479, .k 283151
    1, .k 74763 10196059880, .k 41995 1, .k 25611 49220528784, .k 22411 1, .k 223 1, .k 1623
    7436779519, .k 791 1, .k 663 190196902731, .k 535 1, .k 471 91416876092, .k 279 3607090573272
    , .k 151 1, .k 87 1247148618371, .k 55 1, .k 39 8777991210832, .k 31 1, .k 27 41052276700161,
    .k 87 1, .k 69 68860916608490, .k 117 1, .k 21 65433277186752, .k 8 1, .k 6 78474749496209, .k
    4 1, .k 3 9575881408811365, .k 6 1, .k 0 1295188808094044, .d 2], false⟩

def ckpt15 : RleFullState := ⟨.B, .clean 0 [(26230647, 49220528784), (43007863, 1), (76562295,
    10196059880), (289951607, 1), (306221943, 16080887479), (574657399, 1), (1111528311,
    3278902442), (1761295223, 1), (4446095223, 285528470), (10774804343, 1), (17784372087,
    1019107586), (34964241271, 1), (69323979639, 323903800), (206762933111, 1), (481640840055,
    3190216), (206762933111, 1), (4398651014007, 2829536), (13194744036215, 1), (30786930080631,
    473610), (136340046347127, 1), (83563488213879, 24417), (101155674258295, 1), (136340046347127
    , 34307), (170425059900279, 1), (34085018270583, 9), (34084749835127, 1), (136342820879223, 6)
    , (170462041078647, 1), (34191318711159, 13), (47385458244471, 1619), (51783504755575, 1),
    (60579597777783, 3653), (34191318711159, 1), (425617458199415, 1), (707092434910071, 2872),
    (988567411620727, 1), (1551517365042039, 812), (214511225666423, 1), (21395503223143287, 28),
    (61514483497433975, 1), (85584992052706167, 71), (254647927164107639, 1), (342340009613327223
    , 27), (958028695838227319, 1), (1369360038452968311, 31), (82168436419292535, 1),
    (20595065632538812535, 1), (21909760615247478903, 43), (7991561740213130739, 1),
    (222691182000549570631, 1), (63, 1), (5608898717503354593279, 1)] 2468328002243313095983, [.d
    1, .d 1, .k 5738461 1, .k 58333 1, .k 416733 7436779519, .k 203741 1, .k 170973 190196902731,
    .k 138205 1, .k 121821 91416876092, .k 72669 3607090573272, .k 39901 1, .k 23517 1247148618371
    , .k 15325 1, .k 11229 8777991210832, .k 9181 1, .k 8157 41052276700161, .k 23517 1, .k 18909
    31671798164438, .k 14813 1, .k 4701 37189118444051, .k 7773 1, .k 1629 65433277186752, .k 797
    1, .k 669 78474749496209, .k 541 1, .k 477 9575881408811365, .k 669 1, .k 285
    17162295816727413, .k 477 1, .k 93 246018113982395612, .k 61 1, .k 45 631165860194629366, .k
    32 1, .k 12 4791268012535596513, .k 10 1, .k 9 22342849281290009221, .k 12 1, .k 6
    7588671874192736443, .k 9 1, .k 3 108596472271926337351, .k 6 1, .k 0 206332718429699986606,
    .d 2], false⟩

-- Each chunk reduces 100 (or 80) RLE batches in the kernel via `rfl`.
set_option maxRecDepth 2000000 in
theorem chunk_0 : runBatches 100 ckpt0 = ckpt5 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_1 : runBatches 100 ckpt5 = ckpt10 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_2 : runBatches 100 ckpt10 = ckpt15 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_3 : (runBatches 80 ckpt15).halted = true := rfl

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_3 : costBatches 80 ckpt15 = 932131443777753498525716694644667346522882411249 := rfl

theorem counted_reach_3 : StateHaltsAt First.target_tm ckpt15 932131443777753498525716694644667346522882411249 :=
  counted_final_chunk chunk_3 cost_chunk_3

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_2 : costBatches 100 ckpt10 = 111091883532751998918730984711790130187346565 := rfl

theorem counted_reach_2 : StateHaltsAt First.target_tm ckpt10 932242535661286250524635425629379136653069757814 :=
  counted_chunk_back (b := 100) (k := 111091883532751998918730984711790130187346565) (n := 932131443777753498525716694644667346522882411249) (s1 := ckpt10) (s2 := ckpt15)
    chunk_2 cost_chunk_2 counted_reach_3

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_1 : costBatches 100 ckpt5 = 20898202146405917019016446487890917 := rfl

theorem counted_reach_1 : StateHaltsAt First.target_tm ckpt5 932242535661307148726781831546398153099557648731 :=
  counted_chunk_back (b := 100) (k := 20898202146405917019016446487890917) (n := 932242535661286250524635425629379136653069757814) (s1 := ckpt5) (s2 := ckpt10)
    chunk_1 cost_chunk_1 counted_reach_2

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_0 : costBatches 100 ckpt0 = 141295254433562419116308496 := rfl

theorem counted_reach_0 : StateHaltsAt First.target_tm ckpt0 932242535661307148726923126800831715518673957227 :=
  counted_chunk_back (b := 100) (k := 141295254433562419116308496) (n := 932242535661307148726781831546398153099557648731) (s1 := ckpt0) (s2 := ckpt5)
    chunk_0 cost_chunk_0 counted_reach_1

theorem halts_exact : CanHaltAt First.target_tm (init []) 932242535661307148726923126800831715518673957228 := by
  have h := counted_reach_0
  change CanHaltAt First.target_tm (evalRle First.target_tm ckpt0) 932242535661307148726923126800831715518673957227 at h
  have hInit : ReachesIn First.target_tm 1 (init []) (evalRle First.target_tm ckpt0) := init_reaches_stack
  exact canHaltAt_of_reach hInit h

#print axioms halts_exact
end First

namespace Second

def ckpt0 : RleFullState := ⟨.C, .raw [], [.z 1], false⟩

def ckpt6 : RleFullState := ⟨.C, .raw [.z 1, .k 281358 77415, .k 142094 1, .k 2229006 1, .k
    4440846 48275, .k 29606670 1, .k 17023758 33721, .k 50578190 1, .k 79938318 980, .k 265280270
    1, .k 319753998 203, .k 386862862 1, .k 521080590 6175, .k 789516046 1, .k 1326386958 309, .k
    2270693102 1, .k 5305547838 277, .k 1110974254 1, .k 67113177358 1, .k 84888764430 263, .k
    230838460430 1, .k 339555069966 5, .k 860299088330 1, .k 1358220279870 92, .k 2457731907646 1
    , .k 4656755163198 20, .k 4540718317493 1, .k 1856589531279 1, .z 2], [.k 150286 1, .k 84750
    876511, .k 51982 1, .k 35598 1737322, .k 19214 1, .k 11022 38203784, .k 8974 1, .k 7950
    27434495, .k 4878 42087863, .k 2830 1, .k 1806 73686092, .k 526 1, .k 142 1, .k 174 475716378
    , .k 110 1, .k 78 13551424202, .k 126 1, .k 30 505632912192, .k 14 1, .k 6 47526570402450, .k
    4 1, .k 3 57901138422179, .z 3, .d 2, .k 0 37610989893458, .d 2], false⟩

def ckpt12 : RleFullState := ⟨.BR, .clean 3 [(5399298, 13551424202), (7496450, 1), (11690754,
    475716378), (9593602, 1), (34759426, 1), (118645506, 73686092), (185754370, 1), (319972098,
    42087863), (521298690, 27434495), (588407554, 1), (722625282, 38203784), (1259496194, 1),
    (2333238018, 1737322), (3406979842, 1), (5554463490, 876511), (9849430786, 1), (18439365378,
    77415), (9312559874, 1), (146080424706, 1), (291035570946, 48275), (1940303012610, 1),
    (1115669291778, 32810), (1394586614730, 1), (278917322970, 909), (828673136858, 1),
    (1309709474010, 980), (4346352015578, 1), (5238849575130, 203), (6338361202906, 1),
    (8537384458458, 6175), (12935430969562, 1), (21731523991770, 309), (37203035855066, 1),
    (86926095849690, 277), (18202202249434, 1), (1099582297905370, 1), (1390817516493018, 263),
    (3782057335757018, 1), (5563270266394842, 5), (14095140263270618, 1), (22253081065461978, 6),
    (81803770100545754, 1), (89012324261841114, 8), (190258379573867327, 1), (356049297047364462,
    69), (73427410834671118, 1), (4521950179403093518, 1), (5425513671652212490, 1),
    (4340401297689886786, 1), (91148620044125286401, 1), (15, 1), (1458377920706004582399, 2)]
    364594480176501145522, [.k 8545026 1, .k 2253570 505632912192, .k 1204994 1, .k 680706
    26720150428303, .k 336210 1, .k 21536 1, .k 42549 20806419974146, .k 34357 1, .k 30261
    57901138422180, .k 17973 37610989893458, .k 9781 1, .k 5685 30716371615732, .k 3637 1, .k 2613
    305490132233582, .k 5685 1, .k 4149 270647459772345, .k 3925 1, .k 22 1, .k 267
    139989328324157, .k 107 1, .k 24 1, .k 30 781492533683413, .k 26 1, .k 15 271475135198707, .k
    13 1, .k 12 48671766179730583, .k 15 1, .k 9 94767307651599602, .k 12 1, .k 6
    331887753716974115, .k 3 744220640956988995, .k 1 1, .k 0 18310355970030908204, .d 2], false⟩

def ckpt18 : RleFullState := ⟨.DR0, .raw [.z 3], [.d 1, .z 637191343783878439541550, .d 2, .d 1,
    .k 53511727938691907386159 1, .k 93336186925184309857071 9, .k 55083803111267391840815 1, .k
    23334046731296077464111 50, .k 12468773163752969224751 1, .k 5833511682824019329583 8, .k
    5361091877309366616623 1, .k 1458377920706116272687 6, .k 923739112293703303727 1, .k
    364594480178452447791 5, .k 247860909556172014127 1, .k 91148616760886510127 263, .k
    72062225475526410799 1, .k 1192899526618989103 1, .k 5696788617605366319 277, .k
    2438138157797687855 1, .k 1424197156324721199 309, .k 847736404021297711 1, .k
    559506027869585967 6175, .k 415390839793730095 1, .k 343333245755802159 203, .k
    284842525693002287 1, .k 85833120088801839 980, .k 54307922697208367 1, .k 18279125678244399
    909, .k 91395628383027759 1, .k 73116502706045487 8, .k 18279125676510767 1, .k
    18279125676511791 32801, .k 31789924558623279 1, .k 4768326794400303 48275, .k
    2393381678404143 1, .k 152576980996655 1, .k 302110562374191 77415, .k 161373074018863 1, .k
    91004329841199 876511, .k 55819957752367 1, .k 38227771707951 1737322, .k 20635585663535 1, .k
    11839492641327 38203784, .k 9640469385775 1, .k 8540957757999 27434495, .k 5242422874671
    42087863, .k 3043399619119 1, .k 1943887991343 73686092, .k 569498456623 1, .k 157181596207 1
    , .k 191541334575 475716378, .k 122821857839 1, .k 88462119471 13551424202, .k 140001727023 1
    , .k 36922511919 505632912192, .k 19742642735 1, .k 11152708143 24723210206458, .z 9034176083
    , .d 1, .z 529633014, .d 2, .d 1, .k 2788177035 1996940221844, .k 1377121419 1, .k 88216715 1
    , .k 174285963 20806419974146, .k 140731531 1, .k 123954315 57901138422180, .k 73622667
    37610989893458, .k 40068235 1, .k 23291019 30716371615732, .k 14902411 1, .k 10708107
    305490132233582, .k 23291019 1, .k 16999563 270647459772345, .k 16082059 1, .k 95371 1, .k
    1098891 139989328324157, .k 443531 1, .k 103563 1, .k 128139 781492533683413, .k 111755 1, .k
    66699 271475135198707, .k 58507 1, .k 54411 48671766179730583, .k 66699 1, .k 42123
    94767307651599602, .k 54411 1, .k 29835 331887753716974115, .k 17547 744220640956988995, .k
    9355 1, .k 5259 382904836146532053728, .k 3211 1, .k 2187 210157523808992004318, .k 1931 1, .k
    651 2160111270177901513702, .k 523 1, .k 459 660481848050345900758, .z 87, .d 1, .z 92, .d 2,
    .d 1, .k 114 9040449275367983386986, .k 66 906038693021585505429, .k 41 1, .k 15
    6063759545596197098728, .k 7 1, .k 3 30646279106479104971761, .k 1 1, .k 0
    1009331069384952120084451, .d 2], false⟩

def ckpt24 : RleFullState := ⟨.C, .raw [.z 1, .k 11175430935936220053061216 1, .k
    203498126670575412323054098 1, .k 382305021645554933172033474 33, .k
    188683387653217877438607425 1, .z 2], [.k 23894063852847183323252097 4, .k
    10778816692974141806191745 1, .k 5973515963211795830813313 8, .k 3192005929920760121537153 1,
    .k 1493378990802948948374145 8, .k 1372439520591197853856385 1, .k 373344747700765765808769 6
    , .k 236477212747188045755009 1, .k 93336186925683826635393 5, .k 63452392846380035617409 1,
    .k 23334045890786946593409 263, .k 18447929721734761165441 1, .k 305382278814461211265 1, .k
    1458377886106973778561 277, .k 624163368396208091777 1, .k 364594472019128627841 309, .k
    217020519429452214913 1, .k 143233543134614008449 6175, .k 106340054987194905217 1, .k
    87893310913485353601 203, .k 72919686577408586369 1, .k 21973278742733271681 980, .k
    13902828210485342849 1, .k 4679456173630567041 909, .k 23397280866055107201 1, .k
    18717824692747645569 8, .k 4679456173186757249 1, .k 4679456173187019393 32801, .k
    8138220687007560321 1, .k 1220691659366478465 48275, .k 612705709671461505 1, .k
    39059707135144577 1, .k 77340303967793793 77415, .k 41311506948829825 1, .k 23297108439347841
    876511, .k 14289909184606849 1, .k 9786309557236353 1737322, .k 5282709929865857 1, .k
    3030910116180609 38203784, .k 2467960162759297 1, .k 2186485186048641 27434495, .k
    1342060255916673 42087863, .k 779110302495361 1, .k 497635325784705 73686092, .k
    145791604896385 1, .k 40238488629889 1, .k 49034581652097 475716378, .k 31442395607681 1, .k
    22646302585473 13551424202, .k 35840442118785 1, .k 9452163052161 505632912192, .k
    5054116541057 1, .k 2855093285505 26720150428303, .k 1410172334721 1, .k 90333917825 1, .k
    178468827777 20806419974146, .k 144109089409 1, .k 126929220225 57901138422180, .k 75389612673
    37610989893458, .k 41029874305 1, .k 23850005121 30716371615732, .k 15260070529 1, .k
    10965103233 305490132233582, .k 23850005121 1, .k 17407554177 270647459772345, .k 16468030081
    1, .k 97661569 1, .k 1125266049 139989328324157, .k 454177409 1, .k 106050177 1, .k 131216001
    781492533683413, .k 114438785 1, .k 68301441 271475135198707, .k 59912833 1, .k 55718529
    48671766179730583, .k 68301441 1, .k 43135617 94767307651599602, .k 55718529 1, .k 30552705
    331887753716974115, .k 17969793 744220640956988995, .k 9581185 1, .k 5386881
    7072824145170092509, .k 5265677 1, .k 1346721 176244060668935040975, .k 350513 1, .k 336681
    67361141208737850269, .k 123857 1, .k 84189 132226810123689069972, .k 51421 1, .k 35037
    210157523808992004318, .k 30941 1, .k 10461 2160111270177901513702, .k 8413 1, .k 7389
    660481848050345900758, .k 1437 1, .k 413 1, .k 501 9040449275367983386986, .k 309
    906038693021585505429, .k 209 1, .k 105 6063759545596197098728, .k 73 1, .k 57
    30646279106479104971761, .k 49 1, .k 45 1009331069384952120084451, .k 57 1, .k 33
    7537176816673596729879974, .k 21 5622837964162795894755808, .k 13 1, .k 9
    39547083232249886800713772, .k 5 1, .k 3 654276377082664764984814935, .k 6 1, .k 0
    1615416730339319185619342344, .d 2], false⟩

def ckpt30 : RleFullState := ⟨.C, .raw [.z 1, .k 817153518059714591113512431 1, .k
    1529220086582219732688209391 8, .k 2759377073401380302385087983 1, .k
    6116880346328878930752538095 4, .k 2860910319599672333583672559 1, .k
    52095520427667305554701850351 1, .k 97870085541262062892040570607 8, .k
    259531341126341969520301487855 1, .k 391480342165048251568162282479 3, .k
    1513521437247345871367607986543 1, .k 1565921368660193006272649129967 4, .k
    4190496403530834217529157521375 1, .k 6263685474640772025090596519919 2, .k
    2515196707816662475441974916831 1, .z 2], [.k 382305021645554930783782383 8, .k
    351344517271346650587235823 1, .k 95576255411396036047046127 6, .k 60538166463280139713283567
    1, .k 23894063852975059618661871 5, .k 16243812568673289118057967 1, .k
    5973515748041458327913967 263, .k 4722670008764098858354159 1, .k 78177863376502070085103 1,
    .k 373344738843385287312879 277, .k 159785822309429271496175 1, .k 93336184836896928728559 309
    , .k 55557252973939767018991 1, .k 36667787042461186164207 6175, .k 27223054076721895736815 1
    , .k 22500687593852250523119 203, .k 18667439763816598111727 1, .k 5625159358139717551599 980
    , .k 3559124021884247770607 1, .k 1197940780449425163759 909, .k 5989703901710107444719 1, .k
    4791763121343397266927 8, .k 1197940780335809857007 1, .k 1197940780335876965871 32801, .k
    2083384495873935443439 1, .k 312497064797818488303 48275, .k 156852661675894146543 1, .k
    9999285026597012975 1, .k 19799117815755212271 77415, .k 10575745778900436463 1, .k
    5964059760473048559 876511, .k 3658216751259354607 1, .k 2505295246652507631 1737322, .k
    1352373742045660655 1, .k 775912989742237167 38203784, .k 631797801666381295 1, .k
    559740207628453359 27434495, .k 343567425514669551 42087863, .k 199452237438813679 1, .k
    127394643400885743 73686092, .k 37322650853475823 1, .k 10301053089252847 1, .k
    12552852902938095 475716378, .k 8049253275567599 1, .k 5797453461882351 13551424202, .k
    9175153182410223 1, .k 2419753741354479 505632912192, .k 1293853834511855 1, .k
    730903881090543 26720150428303, .k 361004117689839 1, .k 23125482964463 1, .k 45688019912175
    20806419974146, .k 36891926889967 1, .k 32493880378863 57901138422180, .k 19299740845551
    37610989893458, .k 10503647823343 1, .k 6105601312239 30716371615732, .k 3906578056687 1, .k
    2807066428911 305490132233582, .k 6105601312239 1, .k 4456333870575 270647459772345, .k
    4215815701999 1, .k 25001362927 1, .k 288068109807 139989328324157, .k 116269417967 1, .k
    27148846575 1, .k 33591297519 781492533683413, .k 29296330223 1, .k 17485170159
    271475135198707, .k 15337686511 1, .k 14263944687 48671766179730583, .k 17485170159 1, .k
    11042719215 94767307651599602, .k 14263944687 1, .k 7821493743 331887753716974115, .k
    4600268271 744220640956988995, .k 2452784623 1, .k 1379042799 7072824145170092509, .k
    1348014575 1, .k 344761839 176244060668935040975, .k 89732591 1, .k 86191599
    67361141208737850269, .k 31708655 1, .k 21553647 132226810123689069972, .k 13165039 1, .k
    8970735 210157523808992004318, .k 7922159 1, .k 2679279 2160111270177901513702, .k 2154991 1,
    .k 1892847 660481848050345900758, .k 369135 1, .k 106991 1, .k 129519 9040449275367983386986,
    .k 80367 906038693021585505429, .k 54767 1, .k 28143 6063759545596197098728, .k 19951 1, .k
    15855 30646279106479104971761, .k 13807 1, .k 12783 1009331069384952120084451, .k 15855 1, .k
    9711 7537176816673596729879974, .k 6639 5622837964162795894755808, .k 4591 1, .k 3567
    39547083232249886800713772, .k 2543 1, .k 2031 538559066387679221350882238, .k 1583 1, .k 495
    115717310694985543633932696, .k 687 1, .k 303 1615416730339319185619342344, .k 495 1, .k 111
    274784465758569372306465281757, .k 79 1, .k 63 507674404248318560861238978904, .k 111 1, .k 15
    2504802967801580957720172775389, .k 7 1, .k 3 6623541416857744891568440848885, .k 1 1, .k 0
    4682218824069723167996109957596, .d 2], false⟩

-- Each chunk reduces 120 (or 140) RLE batches in the kernel via `rfl`.
set_option maxRecDepth 2000000 in
theorem chunk_0 : runBatches 120 ckpt0 = ckpt6 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_1 : runBatches 120 ckpt6 = ckpt12 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_2 : runBatches 120 ckpt12 = ckpt18 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_3 : runBatches 120 ckpt18 = ckpt24 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_4 : runBatches 120 ckpt24 = ckpt30 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_5 : (runBatches 140 ckpt30).halted = true := rfl

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_5 : costBatches 140 ckpt30 = 111579147023070743499704300592284974702869920005095477165368960643559026 := rfl

theorem counted_reach_5 : StateHaltsAt Second.target_tm ckpt30 111579147023070743499704300592284974702869920005095477165368960643559026 :=
  counted_final_chunk chunk_5 cost_chunk_5

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_4 : costBatches 120 ckpt24 = 41558741597296557707835313847078384244549803898290818942960412523 := rfl

theorem counted_reach_4 : StateHaltsAt Second.target_tm ckpt24 111579188581812340796262008427598821781254164554899375456187903603971549 :=
  counted_chunk_back (b := 120) (k := 41558741597296557707835313847078384244549803898290818942960412523) (n := 111579147023070743499704300592284974702869920005095477165368960643559026) (s1 := ckpt24) (s2 := ckpt30)
    chunk_4 cost_chunk_4 counted_reach_5

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_3 : costBatches 120 ckpt18 = 586857001825420845011590159535294766634275645627471626020 := rfl

theorem counted_reach_3 : StateHaltsAt Second.target_tm ckpt18 111579188581812927653263833848443833371413699849666009731833531075597569 :=
  counted_chunk_back (b := 120) (k := 586857001825420845011590159535294766634275645627471626020) (n := 111579188581812340796262008427598821781254164554899375456187903603971549) (s1 := ckpt18) (s2 := ckpt24)
    chunk_3 cost_chunk_3 counted_reach_4

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_2 : costBatches 120 ckpt12 = 84283141587124994566866246824440381552011680157949 := rfl

theorem counted_reach_2 : StateHaltsAt Second.target_tm ckpt12 111579188581812927653348116990030958365980566096490450113385542755755518 :=
  counted_chunk_back (b := 120) (k := 84283141587124994566866246824440381552011680157949) (n := 111579188581812927653263833848443833371413699849666009731833531075597569) (s1 := ckpt12) (s2 := ckpt18)
    chunk_2 cost_chunk_2 counted_reach_3

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_1 : costBatches 120 ckpt6 = 12275087658839159917235050050137260374341947 := rfl

theorem counted_reach_1 : StateHaltsAt Second.target_tm ckpt6 111579188581812927653348117002306046024819726013725500163522803130097465 :=
  counted_chunk_back (b := 120) (k := 12275087658839159917235050050137260374341947) (n := 111579188581812927653348116990030958365980566096490450113385542755755518) (s1 := ckpt6) (s2 := ckpt12)
    chunk_1 cost_chunk_1 counted_reach_2

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem cost_chunk_0 : costBatches 120 ckpt0 = 1482037686119792058095754471315 := rfl

theorem counted_reach_0 : StateHaltsAt Second.target_tm ckpt0 111579188581812927653348117002306046024821208051411619955580898884568780 :=
  counted_chunk_back (b := 120) (k := 1482037686119792058095754471315) (n := 111579188581812927653348117002306046024819726013725500163522803130097465) (s1 := ckpt0) (s2 := ckpt6)
    chunk_0 cost_chunk_0 counted_reach_1

theorem halts_exact : CanHaltAt Second.target_tm (init []) 111579188581812927653348117002306046024821208051411619955580898884568781 := by
  have h := counted_reach_0
  change CanHaltAt Second.target_tm (evalRle Second.target_tm ckpt0) 111579188581812927653348117002306046024821208051411619955580898884568780 at h
  have hInit : ReachesIn Second.target_tm 1 (init []) (evalRle Second.target_tm ckpt0) := init_reaches_stack
  exact canHaltAt_of_reach hInit h

#print axioms halts_exact
end Second

end BB6.Agent17.RleCounted





open BusyBeaver
namespace BB6.Agent17.RleCounted

/-- Convert an exact successful-step certificate to primitive halting score,
without a simulation of the enormous raw tape. -/
theorem canHaltAt_run_score {M : Machine (Fin 2) (Fin 6)} {n : Nat}
    (h : CanHaltAt M (init []) n) :
    (multiStep M (init []) n).isSome = true ∧
      multiStep M (init []) (n+1) = none := by
  obtain ⟨c, hc, hstop⟩ := h
  change multiStep M (init []) n = some c at hc
  constructor
  · rw [hc]; rfl
  · rw [multiStep_succ', hc]
    exact Option.isNone_iff_eq_none.mp hstop

/-- Exact time transfer through the upstream library's canonical embedding. -/
theorem canHaltAt_conjecture_score
    {M : ConjectureMachines.Machine 6 2} {n : Nat}
    (h : CanHaltAt M.toBB (init []) n) :
    (((fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n]
          (some ConjectureMachines.init)).isSome = true) ∧
    (fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n+1]
          (some ConjectureMachines.init) = none := by
  obtain ⟨h₁, h₂⟩ := canHaltAt_run_score h
  rw [ConjectureMachines.init_toBB, ConjectureMachines.multiStep_toBB,
    Option.isSome_map] at h₁
  rw [ConjectureMachines.init_toBB, ConjectureMachines.multiStep_toBB,
    Option.map_eq_none_iff] at h₂
  exact ⟨h₁, h₂⟩

theorem first_source_score :
    let M := BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.machine
    let n := 932242535661307148726923126800831715518673957228
    (((fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n]
          (some ConjectureMachines.init)).isSome = true) ∧
    (fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n+1]
          (some ConjectureMachines.init) = none :=
  canHaltAt_conjecture_score First.halts_exact

theorem second_source_score :
    let M := BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.machine
    let n := 111579188581812927653348117002306046024821208051411619955580898884568781
    (((fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n]
          (some ConjectureMachines.init)).isSome = true) ∧
    (fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n+1]
          (some ConjectureMachines.init) = none :=
  canHaltAt_conjecture_score Second.halts_exact

#print axioms first_source_score
#print axioms second_source_score

end BB6.Agent17.RleCounted
