import Mathlib

/-!
# Exact polynomial summation of the three accelerated SymRun macro costs

This Lean file proves only the **arithmetic summation** under candidate exact
fixed-block primitive costs for F424 and F412; it does NOT by itself prove
those block costs correspond to the original Turing machine. The latter is
the separate source-linked acceptance obligation in the dossier README.

The step recursions below mirror the already-source-proved ruleA_iter,
ruleB_iter and ruleC_iter shapes in upstream Cryptids HaltShared.lean.
All variables represent natural numbers; no truncating subtraction or
untrusted numeric testing appears.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace BB6.Agent11.SymRunCosts

/-- F424: cost of n ordinary Rule-A 66-step blocks. -/
def aIter424 : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, m, k =>
      (140 * m + 32 * (k + n) + 454) + aIter424 n (m + 1) k

/-- F412: cost of n ordinary Rule-A 66-step blocks. -/
def aIter412 : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, m, k =>
      (124 * m + 28 * (k + n) + 408) + aIter412 n (m + 1) k

theorem aIter424_closed (n m k : Nat) :
    aIter424 n m k = n * (140 * m + 32 * k + 86 * n + 368) := by
  induction n generalizing m with
  | zero => simp [aIter424]
  | succ n ih =>
    simp only [aIter424]
    rw [ih]
    ring

theorem aIter412_closed (n m k : Nat) :
    aIter412 n m k = n * (124 * m + 28 * k + 76 * n + 332) := by
  induction n generalizing m with
  | zero => simp [aIter412]
  | succ n ih =>
    simp only [aIter412]
    rw [ih]
    ring

/-- Complete accelerated A macro, including its unique initial 46-step prelude.
    Here n=m+1 is the number of initial/pure block segments, and the entering
    repetition count is K=k+n. -/
theorem aMacro424_closed (m k : Nat) :
    (32 * (k + m) + 314) + aIter424 m 0 k =
      (m + 1) * (32 * (k + (m + 1)) + 54 * (m + 1) + 228) := by
  rw [aIter424_closed]
  ring

theorem aMacro412_closed (m k : Nat) :
    (28 * (k + m) + 284) + aIter412 m 0 k =
      (m + 1) * (28 * (k + (m + 1)) + 48 * (m + 1) + 208) := by
  rw [aIter412_closed]
  ring

/-- C: the left repetition p decreases one and the right k increases two
    in each of n 46-step blocks. The entering repetition is P=p+n+2;
    the entering B1 count is K=k+1. -/
def cIter424 : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, p, k =>
      (76 * (p + n) + 64 * k + 486) + cIter424 n p (k + 2)

def cIter412 : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, p, k =>
      (68 * (p + n) + 56 * k + 434) + cIter412 n p (k + 2)

theorem cIter424_closed (n p k : Nat) :
    cIter424 n p k = n * (76 * p + 64 * k + 102 * n + 384) := by
  induction n generalizing k with
  | zero => simp [cIter424]
  | succ n ih =>
    simp only [cIter424]
    rw [ih]
    ring

theorem cIter412_closed (n p k : Nat) :
    cIter412 n p k = n * (68 * p + 56 * k + 90 * n + 344) := by
  induction n generalizing k with
  | zero => simp [cIter412]
  | succ n ih =>
    simp only [cIter412]
    rw [ih]
    ring

theorem cMacro424_closed (n k : Nat) :
    cIter424 n 0 k = n * (102 * n + 64 * (k + 1) + 320) := by
  rw [cIter424_closed]
  ring

theorem cMacro412_closed (n k : Nat) :
    cIter412 n 0 k = n * (90 * n + 56 * (k + 1) + 288) := by
  rw [cIter412_closed]
  ring

/-- B: c is the *macro separator-pair offset* (AA/AB/BA/BB).
    The fixed-block constant is c+542 for F424 and c+484 for F412.
    A macro's literal prefix count is P=p+2 and B1 count is K=k+n. -/
def bIter424 (c : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | n + 1, p, m, k =>
      (152 * p + 140 * (m + n) + 32 * (k + n) + (c + 542)) +
        bIter424 c n (p + 2) m k

def bIter412 (c : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | n + 1, p, m, k =>
      (136 * p + 124 * (m + n) + 28 * (k + n) + (c + 484)) +
        bIter412 c n (p + 2) m k

theorem bIter424_closed (n p m k c : Nat) :
    bIter424 c n p m k =
      n * (152 * p + 140 * m + 32 * k + 238 * n + c + 304) := by
  induction n generalizing p with
  | zero => simp [bIter424]
  | succ n ih =>
    simp only [bIter424]
    rw [ih]
    ring

theorem bIter412_closed (n p m k c : Nat) :
    bIter412 c n p m k =
      n * (136 * p + 124 * m + 28 * k + 212 * n + c + 272) := by
  induction n generalizing p with
  | zero => simp [bIter412]
  | succ n ih =>
    simp only [bIter412]
    rw [ih]
    ring

theorem bMacro424_closed (n p k c : Nat) :
    bIter424 c n p 0 k =
      n * (206 * n + 152 * (p + 2) + 32 * (k + n) + c) := by
  rw [bIter424_closed]
  ring

theorem bMacro412_closed (n p k c : Nat) :
    bIter412 c n p 0 k =
      n * (184 * n + 136 * (p + 2) + 28 * (k + n) + c) := by
  rw [bIter412_closed]
  ring

/-- Substituting each of the four possible separator-pair offsets gives
    the source-derived constant table without case-by-case iteration. -/
example : (1048 : Nat) = 506 + 542 := by norm_num
example : (978 : Nat) = 436 + 542 := by norm_num
example : (896 : Nat) = 354 + 542 := by norm_num
example : (826 : Nat) = 284 + 542 := by norm_num
example : (942 : Nat) = 458 + 484 := by norm_num
example : (880 : Nat) = 396 + 484 := by norm_num
example : (806 : Nat) = 322 + 484 := by norm_num
example : (744 : Nat) = 260 + 484 := by norm_num

#print axioms aIter424_closed
#print axioms aIter412_closed
#print axioms aMacro424_closed
#print axioms aMacro412_closed
#print axioms cIter424_closed
#print axioms cIter412_closed
#print axioms cMacro424_closed
#print axioms cMacro412_closed
#print axioms bIter424_closed
#print axioms bIter412_closed
#print axioms bMacro424_closed
#print axioms bMacro412_closed

end BB6.Agent11.SymRunCosts
