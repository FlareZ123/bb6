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

#print axioms blank_section_mass_bound
#print axioms blank_section_bounded_iff
end BB6.Agent3
