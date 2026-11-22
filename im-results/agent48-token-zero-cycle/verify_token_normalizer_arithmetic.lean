import Lean

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
Arithmetic replay for the bounded 3-adic token normalizer arising from
D_n(1; [0,0,2]) in the six-state Cryptids source.

This file checks the arithmetic recurrence and concrete instances only.
The source-level correspondence of the U_k transitions is documented in
README.md and still requires a quantified source-module Lean proof.
-/

def zeroDigitStep (x : Nat) : Nat :=
  (8 * x + 39) / 3

/-- Remove initial zero residues. Each zero digit consumes one unit of k. -/
def normalizeToken : Nat → Nat → Nat × Nat
  | 0, x => (0, x)
  | k + 1, x =>
      if x % 3 = 0 then
        normalizeToken k (zeroDigitStep x)
      else
        (k + 1, x)

/-- The first argument is the remaining number of 1s in the token K-list. -/
def normalizeRootIndex (n : Nat) : Nat × Nat :=
  normalizeToken 4 (8 * n + 12)

/-- c-coordinate of the ordinary D_0 stack state after token exit and tail. -/
def normalizedC (k x : Nat) : Nat :=
  let q := x / 3
  let r := 3 + 4 * q
  if x % 3 = 1 then
    2 * r + 2 * k + 7
  else
    2 * r + 5

/-- A residual-two exit retains the suffix [2*k+5]; other exits have no suffix. -/
def normalizedSuffix (k x : Nat) : List Nat :=
  if x % 3 = 2 then [2 * k + 5] else []

def normalizedStack (n : Nat) : Nat × List Nat :=
  let (k, x) := normalizeRootIndex n
  (normalizedC k x, normalizedSuffix k x)

theorem zeroDigitStep_eq (x : Nat) (h : x % 3 = 0) :
    zeroDigitStep x = 8 * (x / 3) + 13 := by
  unfold zeroDigitStep
  omega

example : normalizeRootIndex 8841438 = (2, 502979717) := by decide
example : normalizedStack 8841438 = (1341279251, [9]) := by decide

example : normalizeRootIndex 8129901390942 = (3, 173437896340141) := by decide
example : normalizedStack 8129901390942 = (462501056907059, []) := by decide

example : normalizeRootIndex 1 = (4, 20) := by decide
example : normalizedStack 1 = (59, [13]) := by decide

example : normalizeRootIndex 2 = (4, 28) := by decide
example : normalizedStack 2 = (93, []) := by decide

example : normalizeRootIndex 0 = (2, 133) := by decide
example : normalizedStack 0 = (369, []) := by decide

#eval normalizeRootIndex 8841438
#eval normalizedStack 8841438
#eval normalizeRootIndex 8129901390942
#eval normalizedStack 8129901390942
