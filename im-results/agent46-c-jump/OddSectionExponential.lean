import SectionHaltingBasin
import BounceHaltClosed
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

theorem odd_section_iff_exponential (a k : Nat) (ha : 3≤a) (he : a%2=1) :
    secNext (a,k)=none ↔
      (a<2*k ∧ ∃ n : Nat,
        (2*k-a+3)+3*n+2*(a+3) = 2^(n+1)*(a+3)+5) := by
  rw [odd_a_section_none_iff_level a k ha he]
  constructor
  · rintro ⟨hs,n,hn⟩
    refine ⟨hs,n,?_⟩
    have h := haltLevel_closed (a-1) n
    have hA : a-1+4=a+3 := by omega
    rw [hA] at h
    rw [hn]
    exact h
  · rintro ⟨hs,n,hn⟩
    refine ⟨hs,n,?_⟩
    have h := haltLevel_closed (a-1) n
    have hA : a-1+4=a+3 := by omega
    rw [hA] at h
    omega

#print axioms odd_section_iff_exponential
end BB6.Agent46
