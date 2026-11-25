import Lean

/-!
Experimental recursive grammar for the high-counter blocks in the raw112
F1=0LE residual trace. The finite theorem matches_observed verifies all 38
recorded values (k = 0,...,37) in the kernel. The grammar is a candidate
counter encoding; this file does NOT yet prove that the Turing machine visits
this family for every k or implements the k -> k+1 macro.
-/

namespace BB6.Agent47Raw112HighCounter

abbrev Block := Nat

def oddPrefix : Nat → List Block
  | 0 => [0, 6, 1]
  | 1 => [31, 6, 1]
  | 2 => [1, 30, 1]
  | 3 => [28, 3, 31]
  | 4 => [7, 31, 31]
  | 5 => [31, 31, 31]
  | _ => []

def evenPrefix : Nat → List Block
  | 0 => [0, 0, 0]
  | 1 => [31, 0, 0]
  | 2 => [1, 31, 0]
  | 3 => [28, 1, 31]
  | 4 => [7, 29, 31]
  | 5 => [31, 29, 31]
  | _ => []

def digitPrefix (r nextDigit : Nat) : List Block :=
  if nextDigit % 2 = 1 then oddPrefix r else evenPrefix r

def seed : Nat → List Block
  | 0 => []
  | 1 => [31]
  | 2 => [1, 31]
  | 3 => [28, 1, 31]
  | 4 => [7, 29, 31]
  | 5 => [31, 29, 31]
  | _ => []

def charDigit (c : Char) : Nat := c.toNat - 48

def digits6 (n : Nat) : List Nat :=
  (Nat.toDigits 6 n).reverse.map charDigit

/-- Structural recursion over little-endian base-six digits. -/
def highBlocksDigits : List Nat → List Block
  | [] => []
  | [d] => seed d
  | d :: nextDigit :: rest =>
      digitPrefix d nextDigit ++ highBlocksDigits (nextDigit :: rest)

def highBlocks (n : Nat) : List Block := highBlocksDigits (digits6 n)

theorem highBlocksDigits_step (d nextDigit : Nat) (rest : List Nat) :
    highBlocksDigits (d :: nextDigit :: rest) =
      digitPrefix d nextDigit ++ highBlocksDigits (nextDigit :: rest) := rfl

theorem charDigit_digitChar (d : Nat) (hd : d < 6) :
    charDigit (Nat.digitChar d) = d := by
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  rcases hcases with h | h | h | h | h | h <;> subst d <;> decide

theorem digits6_six (m r : Nat) (hm : 1 ≤ m) (hr : r < 6) :
    digits6 (6 * m + r) = r :: digits6 m := by
  have hlarge : 6 ≤ 6 * m + r := by omega
  unfold digits6
  rw [Nat.toDigits_of_base_le (by decide : 1 < 6) hlarge]
  have hdiv : (6 * m + r) / 6 = m := by omega
  have hmod : (6 * m + r) % 6 = r := by omega
  rw [hdiv, hmod]
  simp [List.reverse_append, charDigit_digitChar r hr]

theorem digits6_head (m : Nat) : (digits6 m).head? = some (m % 6) := by
  by_cases hm : m < 6
  · unfold digits6
    rw [Nat.toDigits_of_lt_base hm]
    have hchar : charDigit (Nat.digitChar m) = m := charDigit_digitChar m hm
    simp [hchar, Nat.mod_eq_of_lt hm]
  · have hlarge : 6 ≤ m := Nat.le_of_not_gt hm
    unfold digits6
    rw [Nat.toDigits_of_base_le (by decide : 1 < 6) hlarge]
    have hchar : charDigit (Nat.digitChar (m % 6)) = m % 6 :=
      charDigit_digitChar (m % 6) (Nat.mod_lt m (by decide))
    simp [List.reverse_append, hchar]

theorem highBlocks_six (m r : Nat) (hm : 1 ≤ m) (hr : r < 6) :
    highBlocks (6 * m + r) = digitPrefix r (m % 6) ++ highBlocks m := by
  rw [highBlocks, digits6_six m r hm hr]
  cases hds : digits6 m with
  | nil =>
    have hh := digits6_head m
    rw [hds] at hh
    simp at hh
  | cons d rest =>
    have hd : d = m % 6 := by
      have hh := digits6_head m
      simpa [hds] using hh
    simp [hds, hd, highBlocks, highBlocksDigits]

theorem mod6_parity (m : Nat) : (m % 6) % 2 = m % 2 := by omega

theorem highBlocks_six_parity (m r : Nat) (hm : 1 ≤ m) (hr : r < 6) :
    highBlocks (6 * m + r) =
      (if m % 2 = 1 then oddPrefix r else evenPrefix r) ++ highBlocks m := by
  rw [highBlocks_six m r hm hr]
  simp [digitPrefix]

theorem digitPrefix_length (r d : Nat) (hr : r < 6) :
    (digitPrefix r d).length = 3 := by
  have hrcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases hrcases with h | h | h | h | h | h <;> subst r
  all_goals by_cases hp : d % 2 = 1 <;> simp [digitPrefix, hp, oddPrefix, evenPrefix]

theorem highBlocks_length_six (m r : Nat) (hm : 1 ≤ m) (hr : r < 6) :
    (highBlocks (6 * m + r)).length = 3 + (highBlocks m).length := by
  rw [highBlocks_six m r hm hr]
  simp [digitPrefix_length r (m % 6) hr]

/-- Exact high-block rows 0..37 copied from the Agent 19 counter trace. -/
def observed : List (List Block) :=
  [ [], [31], [1, 31], [28, 1, 31], [7, 29, 31], [31, 29, 31],
    [0, 6, 1, 31], [31, 6, 1, 31], [1, 30, 1, 31], [28, 3, 31, 31],
    [7, 31, 31, 31], [31, 31, 31, 31], [0, 0, 0, 1, 31],
    [31, 0, 0, 1, 31], [1, 31, 0, 1, 31], [28, 1, 31, 1, 31],
    [7, 29, 31, 1, 31], [31, 29, 31, 1, 31], [0, 6, 1, 28, 1, 31],
    [31, 6, 1, 28, 1, 31], [1, 30, 1, 28, 1, 31], [28, 3, 31, 28, 1, 31],
    [7, 31, 31, 28, 1, 31], [31, 31, 31, 28, 1, 31], [0, 0, 0, 7, 29, 31],
    [31, 0, 0, 7, 29, 31], [1, 31, 0, 7, 29, 31], [28, 1, 31, 7, 29, 31],
    [7, 29, 31, 7, 29, 31], [31, 29, 31, 7, 29, 31], [0, 6, 1, 31, 29, 31],
    [31, 6, 1, 31, 29, 31], [1, 30, 1, 31, 29, 31], [28, 3, 31, 31, 29, 31],
    [7, 31, 31, 31, 29, 31], [31, 31, 31, 31, 29, 31], [0, 0, 0, 0, 6, 1, 31],
    [31, 0, 0, 0, 6, 1, 31] ]

/-- Kernel-checked finite agreement with every high-block row presently observed. -/
theorem matches_observed : (List.range 38).map highBlocks = observed := by decide

#print axioms highBlocksDigits_step
#print axioms charDigit_digitChar
#print axioms digits6_six
#print axioms digits6_head
#print axioms highBlocks_six
#print axioms highBlocks_six_parity
#print axioms highBlocks_length_six
#print axioms matches_observed

end BB6.Agent47Raw112HighCounter
