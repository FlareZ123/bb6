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
