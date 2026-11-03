import Root119Gate

namespace BB6Root119

-- One marked cell seven positions to the left of a synthetic B/0 head.
-- This is NOT a configuration known to be blank-tape reachable.
def oneMarkTape (x : Int) : Bool := decide (x = -7)
def oneMarkSeed : Conf := ⟨.B, 0, oneMarkTape⟩

def oneMarkRun (n : Nat) (c : Option Conf) : Option Conf :=
  match n with
  | 0 => c
  | n+1 => oneMarkRun n (c.bind next)

def oneMarkTerminalSample (o : Option Conf) : Bool :=
  match o with
  | none => false
  | some c => decide (c.q = .A ∧ c.h = -4 ∧ c.tape c.h = true)

theorem oneMark_singleton :
    ∀ x : Int, oneMarkTape x = true ↔ x = -7 := by
  intro x
  simp [oneMarkTape]

theorem oneMark_B_zero :
    oneMarkSeed.q = .B ∧ oneMarkSeed.tape oneMarkSeed.h = false := by
  decide

set_option maxRecDepth 8192 in
theorem oneMark_stop202 :
    oneMarkTerminalSample (oneMarkRun 202 (some oneMarkSeed)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem oneMark_none203 :
    oneMarkRun 203 (some oneMarkSeed) = none := by
  decide +kernel

/-- An artificial B/0 initial tape with EXACTLY one marked cell (at -7)
    executes 202 legal steps and then queries the undefined A/1 edge. -/
theorem oneMark_exact_halter :
    (∀ x : Int, oneMarkSeed.tape x = true ↔ x = -7) ∧
    ∃ c, oneMarkRun 202 (some oneMarkSeed) = some c ∧ next c = none := by
  constructor
  · exact oneMark_singleton
  · cases he : oneMarkRun 202 (some oneMarkSeed) with
    | none =>
      have h := oneMark_stop202
      simp [oneMarkTerminalSample, he] at h
    | some c =>
      have h := oneMark_stop202
      rw [he] at h
      have hi : c.q = .A ∧ c.h = -4 ∧ c.tape c.h = true := by
        exact of_decide_eq_true (by simpa [oneMarkTerminalSample] using h)
      refine ⟨c,rfl,?_⟩
      exact (next_none_iff c).mpr ⟨hi.1, hi.2.2⟩

#print axioms BB6Root119.oneMark_exact_halter
end BB6Root119
