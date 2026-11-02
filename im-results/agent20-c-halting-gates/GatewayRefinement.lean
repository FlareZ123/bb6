import BlankParam
import GateArithmetic
import Agent38SectionParity

namespace Agent20Gate
open BB6.Agent46

/-- A source-connected halting section cannot have odd right counter and
    counter sum equal to two modulo four. The exceptional blank root (5,1)
    has a nonhalting section successor. -/
theorem no_parity_halting_gate (t a k : Nat)
    (hr : BB6.Agent8Section.run secNext t (some (5,1))=some (a,k))
    (hs : secNext (a,k)=none)
    (hk : k%2=1) (hmod : (a+k)%4=2) : False := by
  have hroot := BB6Agent38.blank_section_mod4 t a k hr hk hmod
  have hsroot : secNext (5,1)=none := by simpa only [hroot] using hs
  exact (by decide : secNext (5,1)≠none) hsroot

/-- Every low halting parameter m=1 mod 4 is blank-unreachable. -/
theorem low_family_unreachable (m k t : Nat)
    (he : k+3*m+4=2^(2*m+3)) (hm : m%4=1) :
    BB6.Agent8Section.run secNext t (some (5,1)) ≠ some (1,k) := by
  intro hr
  have ⟨hk, hmod⟩ := low_mod_one m k he hm
  have hs : secNext (1,k)=none :=
    (BB6.Agent15.section_halts_iff_parametric 1 k).mpr
      (Or.inr (Or.inl ⟨rfl,m,he⟩))
  exact no_parity_halting_gate t 1 k hr hs hk hmod

/-- Every higher halting parameter pair j+m=0 mod 4 is blank-unreachable. -/
theorem high_family_unreachable (j m k t : Nat)
    (he : k+j+3*m+5=2^(2*m+2)*(j+3)) (hm : (j+m)%4=0) :
    BB6.Agent8Section.run secNext t (some (5,1)) ≠ some (2*j+3,k) := by
  intro hr
  have ⟨hk,hmod⟩ := high_mod_zero j m k he hm
  have hs : secNext (2*j+3,k)=none :=
    (BB6.Agent15.section_halts_iff_parametric (2*j+3) k).mpr
      (Or.inr (Or.inr ⟨j,m,rfl,he⟩))
  exact no_parity_halting_gate t (2*j+3) k hr hs hk hmod

/-- Exact refinement of the source-connected two-family Machine C stopping
    criterion. Remaining parameter families are still unresolved. -/
theorem blank_halts_iff_refined :
    BB6.CReachBridge.RunHalts ↔
      ∃ t a k,
        BB6.Agent8Section.run secNext t (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, m%4≠1 ∧ k+3*m+4=2^(2*m+3)) ∨
         (∃ j m, a=2*j+3 ∧ (j+m)%4≠0 ∧
           k+j+3*m+5=2^(2*m+2)*(j+3))) := by
  constructor
  · intro h
    obtain ⟨t,a,k,hr,hgate⟩ := BB6.Agent15.blank_halts_iff_two_parametric_families.mp h
    refine ⟨t,a,k,hr,?_⟩
    rcases hgate with ⟨ha,m,he⟩ | ⟨j,m,ha,he⟩
    · subst a
      refine Or.inl ⟨rfl,m,?_,he⟩
      intro hm
      exact low_family_unreachable m k t he hm hr
    · subst a
      refine Or.inr ⟨j,m,rfl,?_,he⟩
      intro hm
      exact high_family_unreachable j m k t he hm hr
  · rintro ⟨t,a,k,hr,hgate⟩
    apply BB6.Agent15.blank_halts_iff_two_parametric_families.mpr
    refine ⟨t,a,k,hr,?_⟩
    rcases hgate with ⟨ha,m,_,he⟩ | ⟨j,m,ha,_,he⟩
    · exact Or.inl ⟨ha,m,he⟩
    · exact Or.inr ⟨j,m,ha,he⟩

#print axioms low_family_unreachable
#print axioms high_family_unreachable
#print axioms blank_halts_iff_refined
end Agent20Gate
