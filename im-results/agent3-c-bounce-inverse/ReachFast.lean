import SectionMassOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3

open BB6.Agent46

/-- A single-pass tail-recursive exact fixed-target checker. This runs one
    original source section transition per tested time; avoids re-evaluating
    every prefix separately, unlike the elementary bounded existential. -/
def reachesFuel (target : Nat × Nat) :
    Nat → Option (Nat × Nat) → Bool
  | 0,s => decide (s=some target)
  | n+1,s =>
      decide (s=some target) || reachesFuel target n (s.bind secNext)

private theorem run_succ_head (n : Nat) (s : Option (Nat×Nat)) :
    BB6.Agent8Section.run secNext (n+1) s =
      BB6.Agent8Section.run secNext n (s.bind secNext) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [BB6.Agent8Section.run]
    rw [ih]
    simp [BB6.Agent8Section.run, Option.bind_assoc]

/-- Every index up to the fuel is covered, and no other index is accepted. -/
theorem reachesFuel_correct (target : Nat×Nat)
    (n : Nat) (s : Option (Nat×Nat)) :
    reachesFuel target n s = true ↔
      ∃ i : Nat, i≤n ∧
        BB6.Agent8Section.run secNext i s=some target := by
  induction n generalizing s with
  | zero =>
    simp [reachesFuel,BB6.Agent8Section.run]
  | succ n ih =>
    simp only [reachesFuel, Bool.or_eq_true, decide_eq_true_eq]
    rw [ih]
    constructor
    · intro h
      rcases h with h0 | ⟨i,hi,hrt⟩
      · exact ⟨0,by omega,by simpa [BB6.Agent8Section.run] using h0⟩
      · exact ⟨i+1,by omega,by simpa [run_succ_head] using hrt⟩
    · rintro ⟨i,hi,hrt⟩
      cases i with
      | zero =>
        exact Or.inl (by simpa [BB6.Agent8Section.run] using hrt)
      | succ i =>
        right
        refine ⟨i,by omega,?_⟩
        simpa [run_succ_head] using hrt

/-- Efficient exact Boolean decision for arbitrary fixed blank-section
    target coordinates, relying on source-proven strict mass growth. -/
def blankReachFast (a k : Nat) : Bool :=
  reachesFuel (a,k) ((a+2*k-7)/2) (some (5,1))

theorem blankReachFast_correct (a k : Nat) :
    blankReachFast a k = true ↔
      ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
        some (a,k) := by
  rw [blankReachFast,reachesFuel_correct]
  constructor
  · rintro ⟨n,_,h⟩
    exact ⟨n,h⟩
  · rintro ⟨n,h⟩
    have hb := blank_section_mass_bound n a k h
    exact ⟨n,by omega,h⟩

/-- Source-faithful first-prefix sanity checks, kernel evaluated. -/
example : blankReachFast 5 1 = true := by decide
example : blankReachFast 3 4 = true := by decide
example : blankReachFast 1 4 = false := by decide

#print axioms reachesFuel_correct
#print axioms blankReachFast_correct
end BB6.Agent3
