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

#print axioms root42_valid
#print axioms blank_root42
end BB6.Row109Locality
