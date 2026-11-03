import PositiveMassOriginal
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1ForwardMass
open BB6.Agent46

/-- Each authentic blank-origin Machine C section increases mass by at least
    four: combine Agent38's globally positive right counter invariant with the
    complete positive-right source return arithmetic. -/
theorem blank_mass_at_least_four_per_section (n a k : Nat)
    (h : BB6.Agent8Section.run secNext n (some (5,1)) = some (a,k)) :
    7+4*n ≤ a+2*k := by
  induction n generalizing a k with
  | zero =>
      simp [BB6.Agent8Section.run] at h
      omega
  | succ n ih =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨u,v⟩
          have ht : secNext (u,v) = some (a,k) := by
            simpa [BB6.Agent8Section.run,hp] using h
          have hpos := BB6Agent38.blank_section_positive n u v hp
          have hstep := section_mass_four_if_right_positive u v a k (by omega) ht
          have hbefore := ih u v hp
          omega

/-- Sharp linear necessary index bound for arbitrary blank-reachable states. -/
theorem blank_section_index_upper (n a k : Nat)
    (h : BB6.Agent8Section.run secNext n (some (5,1)) = some (a,k)) :
    n ≤ (a+2*k-7)/4 := by
  have hm := blank_mass_at_least_four_per_section n a k h
  omega

#print axioms blank_mass_at_least_four_per_section
#print axioms blank_section_index_upper
end BB6.Agent1ForwardMass
