import Root119Gate

namespace BB6Root119

def fourMarkTape (x : Int) : Bool := decide (x = -6 ∨ x = -5 ∨ x = -3 ∨ x = -2)
def fourMarkSeed : Conf := ⟨.B,0,fourMarkTape⟩

def fourMarkRun : Nat → Option Conf → Option Conf
  | 0,c => c
  | n+1,c => fourMarkRun n (c.bind next)

def fourMarkBad17 (o : Option Conf) : Bool :=
  match o with
  | none => false
  | some c => decide (c.q = .B ∧ c.h = 3 ∧ c.tape c.h = false ∧
      c.tape (-6) = true ∧ c.tape (-5) = true ∧
      c.tape (-4) = false ∧ c.tape (-3) = false)

def fourMarkTerminal34 (o : Option Conf) : Bool :=
  match o with
  | none => false
  | some c => decide (c.q = .A ∧ c.h = -6 ∧ c.tape c.h = true)

theorem fourMark_no1000_left :
    ∀ x : Int, x+3 < fourMarkSeed.h →
      ¬(fourMarkSeed.tape x = true ∧ fourMarkSeed.tape (x+1) = false ∧
        fourMarkSeed.tape (x+2) = false ∧ fourMarkSeed.tape (x+3) = false) := by
  intro x hx ⟨a,b,c,d⟩
  simp [fourMarkSeed,fourMarkTape] at *
  omega

theorem fourMark_no1100_left :
    ∀ x : Int, x+3 < fourMarkSeed.h →
      ¬(fourMarkSeed.tape x = true ∧ fourMarkSeed.tape (x+1) = true ∧
        fourMarkSeed.tape (x+2) = false ∧ fourMarkSeed.tape (x+3) = false) := by
  intro x hx ⟨a,b,c,d⟩
  simp [fourMarkSeed,fourMarkTape] at *
  omega

theorem fourMark_no1110_left :
    ∀ x : Int, x+3 < fourMarkSeed.h →
      ¬(fourMarkSeed.tape x = true ∧ fourMarkSeed.tape (x+1) = true ∧
        fourMarkSeed.tape (x+2) = true ∧ fourMarkSeed.tape (x+3) = false) := by
  intro x hx ⟨a,b,c,d⟩
  simp [fourMarkSeed,fourMarkTape] at *
  omega

set_option maxRecDepth 4096 in
theorem fourMark_bad17 : fourMarkBad17 (fourMarkRun 17 (some fourMarkSeed)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem fourMark_terminal34 : fourMarkTerminal34 (fourMarkRun 34 (some fourMarkSeed)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem fourMark_none35 : fourMarkRun 35 (some fourMarkSeed) = none := by
  decide +kernel

/-- A four-mark synthetic B/0 tape starts with no left-side 1000, 1100,
    or 1110. The shield nevertheless fails at step 17 and A/1 halts at 34. -/
theorem fourMark_exact_halter :
    (∀ x : Int, x+3 < fourMarkSeed.h →
      ¬(fourMarkSeed.tape x = true ∧ fourMarkSeed.tape (x+1) = true ∧
        fourMarkSeed.tape (x+2) = false ∧ fourMarkSeed.tape (x+3) = false)) ∧
    ∃ c, fourMarkRun 34 (some fourMarkSeed) = some c ∧ next c = none := by
  constructor
  · exact fourMark_no1100_left
  · cases he : fourMarkRun 34 (some fourMarkSeed) with
    | none =>
      have h := fourMark_terminal34
      simp [fourMarkTerminal34,he] at h
    | some c =>
      have h := fourMark_terminal34
      rw [he] at h
      have hi : c.q = .A ∧ c.h = -6 ∧ c.tape c.h = true := by
        exact of_decide_eq_true (by simpa [fourMarkTerminal34] using h)
      refine ⟨c,rfl,?_⟩
      rcases c with ⟨q,p,t⟩
      obtain ⟨hq,_,hb⟩ := hi
      change q = .A at hq
      subst q
      change t p = true at hb
      simp [next,hb]

#print axioms BB6Root119.fourMark_exact_halter
#print axioms BB6Root119.fourMark_no1000_left
#print axioms BB6Root119.fourMark_no1100_left
#print axioms BB6Root119.fourMark_no1110_left
end BB6Root119
