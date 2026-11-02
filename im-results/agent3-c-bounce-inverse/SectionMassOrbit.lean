import SectionMassStrict
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3

open BB6.Agent46

/-- Every genuinely blank-reached Machine C zero-right-counter section point
    has weighted mass at least 7+2n after n completed returns. -/
theorem blank_section_mass_bound (n a k : Nat)
    (h : BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)) :
    7+2*n≤a+2*k := by
  induction n generalizing a k with
  | zero =>
    simp [BB6.Agent8Section.run] at h
    omega
  | succ n ih =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨b,c⟩
      have ht : secNext (b,c)=some (a,k) := by
        simpa [BB6.Agent8Section.run,hp] using h
      have hr := section_mass_strict b c a k ht
      have hprev := ih b c hp
      omega

/-- Exact bound turning fixed-target blank reachability into a finite search:
    every witnessing section time n is at most floor((a+2k-7)/2).
    This does NOT settle the unbounded two-parameter halting locus. -/
theorem blank_section_bounded_iff (a k : Nat) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)) ↔
    (∃ n, n≤(a+2*k-7)/2 ∧
      BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)) := by
  constructor
  · rintro ⟨n,h⟩
    have hmass := blank_section_mass_bound n a k h
    exact ⟨n,by omega,h⟩
  · rintro ⟨n,_,h⟩
    exact ⟨n,h⟩


/-- Computable, certified search for a fixed Machine C section target.
    The finite existential is implemented by the standard bounded Nat
    quantifier Decidable, not by classical choice. -/
def blank_section_reach_decidable (a k : Nat) :
    Decidable (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)) := by
  let M := (a+2*k-7)/2
  have hiff :
      (∃ n, n<M+1 ∧
        BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)) ↔
      (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)) := by
    rw [blank_section_bounded_iff]
    constructor
    · rintro ⟨n,hn,h⟩
      exact ⟨n,by dsimp [M] at hn ⊢; omega,h⟩
    · rintro ⟨n,hn,h⟩
      exact ⟨n,by dsimp [M] at hn ⊢; omega,h⟩
  exact decidable_of_iff
    (∃ n, n<M+1 ∧
      BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)) hiff

/-- Executable theorem-backed Boolean fixed-target reachability decision. -/
def blank_section_reachable (a k : Nat) : Bool :=
  @decide _ (blank_section_reach_decidable a k)

theorem blank_section_reachable_correct (a k : Nat) :
    blank_section_reachable a k = true ↔
      (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)) := by
  simp [blank_section_reachable,decide_eq_true_eq]

#print axioms blank_section_reachable_correct

#print axioms blank_section_mass_bound
#print axioms blank_section_bounded_iff
end BB6.Agent3
