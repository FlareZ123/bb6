import Root119GlobalShield

namespace BB6Root119

-- Deliberately synthetic tape, not blank-root reachable.
def fakeTape (x : Int) : Bool :=
  decide (x = -9 ∨ x = -8 ∨ x = -6 ∨ x = -5 ∨ x = -3)

def fakeB : Conf := ⟨.B,0,fakeTape⟩

def run (n : Nat) (c : Option Conf) : Option Conf :=
  match n with
  | 0 => c
  | n+1 => run n (c.bind next)

theorem fakeB_zero : BZero fakeB := by simp [BZero, fakeB, fakeTape]

theorem fakeB_no_left1100 : ¬HasLeft1100 fakeB := by
  rintro ⟨x,hpos,h1,h2,h3,h4⟩
  have hx1 : x = -9 ∨ x = -8 ∨ x = -6 ∨ x = -5 ∨ x = -3 := by
    simpa [fakeB, fakeTape] using h1
  have hx2 : x+1 = -9 ∨ x+1 = -8 ∨ x+1 = -6 ∨ x+1 = -5 ∨ x+1 = -3 := by
    simpa [fakeB, fakeTape] using h2
  have hx4 : x+3 ≠ -9 ∧ x+3 ≠ -8 ∧ x+3 ≠ -6 ∧ x+3 ≠ -5 ∧ x+3 ≠ -3 := by
    simpa [fakeB, fakeTape] using h4
  omega

def goodSample (o : Option Conf) : Bool :=
  match o with
  | none => false
  | some c => decide (c.q = .B ∧ c.h = 2 ∧ c.tape c.h = false ∧
      c.tape (-9) = true ∧ c.tape (-8) = true ∧
      c.tape (-7) = false ∧ c.tape (-6) = false)

set_option maxRecDepth 2048 in
theorem fake_return22_compute : goodSample (run 22 (some fakeB)) = true := by
  decide +kernel

/-- A B/0 configuration with no forbidden left-1100 word can return to
    another B/0 configuration with that very word. No blank-root assertion. -/
theorem no_left1100_not_closed_under_B_returns :
  BZero fakeB ∧ ¬HasLeft1100 fakeB ∧
  ∃ c, run 22 (some fakeB) = some c ∧ BZero c ∧ HasLeft1100 c := by
  refine ⟨fakeB_zero,fakeB_no_left1100,?_⟩
  cases he : run 22 (some fakeB) with
  | none =>
    have hbad := fake_return22_compute
    simp [goodSample, he] at hbad
  | some c =>
    have hsample := fake_return22_compute
    rw [he] at hsample
    have heq : c.q = .B ∧ c.h = 2 ∧ c.tape c.h = false ∧
       c.tape (-9) = true ∧ c.tape (-8) = true ∧
       c.tape (-7) = false ∧ c.tape (-6) = false := by
      exact of_decide_eq_true (by simpa [goodSample] using hsample)
    obtain ⟨hq,hh,h0,h1,h2,h3,h4⟩ := heq
    refine ⟨c,rfl,⟨hq,h0⟩, -9,by omega,?_,?_,?_,?_⟩
    · exact h1
    · exact h2
    · exact h3
    · exact h4

#print axioms BB6Root119.no_left1100_not_closed_under_B_returns
end BB6Root119
