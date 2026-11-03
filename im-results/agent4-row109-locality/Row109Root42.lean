import Row109Safe

namespace BB6.Row109Locality

-- The published BlockSimulator starts at base_steps = 42, with
-- macro word L X c> D0 M K R. This theorem checks the exact 42 raw
-- primitive transitions from the standard blank-tape, initial-A root.
-- Binary decoded word from tape coordinate -3 onward: 11011001110.
def root42 : Certificate :=
  { beforeBits := 0, initialState := 0, initialHead := 0,
    afterBits := 923, afterShift := -3, finalState := 2,
    finalHead := 0, steps := 42, lo := -3, hi := 6 }

theorem root42_valid : accepted root42 = true := by decide

-- Grounded exact original blank-root reachable state at raw time 42.
theorem blank_root42 :
    let c : Cfg := {st := 0, h := 0, tape := fun _ => false}
    let out := run 42 c
    out.st = 2 ∧ out.h = 0 ∧
    ∀ p, out.tape p =
      (if -3 ≤ p ∧ p ≤ 6 then wordTape 923 (p+3) else false) := by
  have ht : ∀ p, InWindow root42.lo root42.hi p →
      (fun _ : Int => false) p = wordTape root42.beforeBits p := by
    intro p _
    simp [root42, wordTape]
  simpa [root42] using accepted_sound root42 root42_valid (fun _ => false) ht

theorem word923_outside (p : Int) (hp : ¬(-3 ≤ p ∧ p ≤ 6)) :
    wordTape 923 (p+3) = false := by
  by_cases hleft : p < -3
  · have hneg : p + 3 < 0 := by omega
    simp [wordTape, hneg]
  · have hhigh : 10 ≤ (p+3).toNat := by omega
    have hpow : 923 < 2 ^ (p+3).toNat := by
      have hle : 2^10 ≤ 2^(p+3).toNat :=
        Nat.pow_le_pow_right (by decide) hhigh
      omega
    have hshift : 923 >>> (p+3).toNat = 0 :=
      Nat.shiftRight_eq_zero 923 _ hpow
    have hnonnegative : ¬ p+3 < 0 := by omega
    simp [wordTape, hnonnegative, Nat.testBit, hshift]

theorem blank_root42_exact_word :
    let out := run 42 {st := 0, h := 0, tape := fun _ => false}
    out.st = 2 ∧ out.h = 0 ∧
    ∀ p, out.tape p = wordTape 923 (p+3) := by
  have h := blank_root42
  dsimp at h ⊢
  rcases h with ⟨hs,hh,ht⟩
  refine ⟨hs, hh, ?_⟩
  intro p
  rw [ht]
  by_cases hp : -3 ≤ p ∧ p ≤ 6
  · simp [hp]
  · simp [hp, word923_outside p hp]

#print axioms blank_root42_exact_word
#print axioms root42_valid
#print axioms blank_root42
end BB6.Row109Locality
