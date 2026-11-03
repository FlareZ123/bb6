import Root119Gate

namespace BB6Root119

-- Imported source table is exactly:
-- 1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD.
-- This starting configuration is deliberately artificial, not blank reachable.
def twoMarkTape (x : Int) : Bool := decide (x = -4 ∨ x = 2)
def twoMarkSeed : Conf := ⟨.B, 0, twoMarkTape⟩

def twoMarkRun (n : Nat) (c : Option Conf) : Option Conf :=
  match n with
  | 0 => c
  | n+1 => twoMarkRun n (c.bind next)

def twoMarkReturnSample (o : Option Conf) : Bool :=
  match o with
  | none => false
  | some c => decide
    (c.q = .B ∧ c.h = 5 ∧ c.tape c.h = false ∧
      c.tape (-4) = true ∧ c.tape (-3) = true ∧
      c.tape (-2) = false ∧ c.tape (-1) = false)

def twoMarkTerminalSample (o : Option Conf) : Bool :=
  match o with
  | none => false
  | some c => decide (c.q = .A ∧ c.h = -4 ∧ c.tape c.h = true)

theorem twoMark_no_adjacent :
    ∀ x : Int, ¬(twoMarkTape x = true ∧ twoMarkTape (x+1) = true) := by
  intro x ⟨ha, hb⟩
  simp [twoMarkTape] at ha hb
  omega

theorem twoMark_seed_B_zero :
    twoMarkSeed.q = .B ∧ twoMarkSeed.tape twoMarkSeed.h = false := by
  decide

theorem twoMark_seed_no_1100_left :
    ¬∃ x : Int, x+3 < twoMarkSeed.h ∧ twoMarkSeed.tape x = true ∧
      twoMarkSeed.tape (x+1) = true ∧
      twoMarkSeed.tape (x+2) = false ∧
      twoMarkSeed.tape (x+3) = false := by
  rintro ⟨x, _, h1, h2, _, _⟩
  exact twoMark_no_adjacent x ⟨h1,h2⟩

theorem twoMark_seed_no_11011_left :
    ¬∃ x : Int, x+4 < twoMarkSeed.h ∧ twoMarkSeed.tape x = true ∧
      twoMarkSeed.tape (x+1) = true ∧
      twoMarkSeed.tape (x+2) = false ∧
      twoMarkSeed.tape (x+3) = true ∧
      twoMarkSeed.tape (x+4) = true := by
  rintro ⟨x, _, h1, h2, _, _, _⟩
  exact twoMark_no_adjacent x ⟨h1,h2⟩

set_option maxRecDepth 4096 in
theorem twoMark_return27 :
    twoMarkReturnSample (twoMarkRun 27 (some twoMarkSeed)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem twoMark_stop44 :
    twoMarkTerminalSample (twoMarkRun 44 (some twoMarkSeed)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem twoMark_none45 :
    twoMarkRun 45 (some twoMarkSeed) = none := by
  decide +kernel

/-- A two-mark, globally-adjacency-free artificial B/0 seed reaches the
    authentic A/1 undefined transition in exactly 44 successful steps. -/
theorem twoMark_exact_halter :
    (∀ x : Int, ¬(twoMarkSeed.tape x = true ∧
      twoMarkSeed.tape (x+1) = true)) ∧
    ∃ c, twoMarkRun 44 (some twoMarkSeed) = some c ∧ next c = none := by
  constructor
  · exact twoMark_no_adjacent
  · cases he : twoMarkRun 44 (some twoMarkSeed) with
    | none =>
      have h := twoMark_stop44
      simp [twoMarkTerminalSample, he] at h
    | some c =>
      have h := twoMark_stop44
      rw [he] at h
      have hi : c.q = .A ∧ c.h = -4 ∧ c.tape c.h = true := by
        exact of_decide_eq_true (by simpa [twoMarkTerminalSample] using h)
      refine ⟨c,rfl,?_⟩
      exact (next_none_iff c).mpr ⟨hi.1,hi.2.2⟩

#print axioms BB6Root119.twoMark_exact_halter
#print axioms BB6Root119.twoMark_return27
end BB6Root119
