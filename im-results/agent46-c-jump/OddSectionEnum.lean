import SectionHaltingBasin
import BounceHaltingInputs
import Lean.Elab.Tactic.Omega
namespace BB6.Agent46

theorem odd_section_none_iff_haltingK (a k : Nat) (ha : 3≤a) (he : a%2=1) :
    secNext (a,k)=none ↔ ∃ j, k=oddHaltingK a j := by
  constructor
  · intro hh
    obtain ⟨hsmall,n,hn⟩ := (odd_a_section_none_iff_level a k ha he).mp hh
    have hC : (2*k-a+3)%2=0 := by omega
    have hLevel : (haltLevel (a-1) n)%2=(n+1)%2 := haltLevel_mod_two n (a-1)
    have hOdd : n%2=1 := by omega
    have hSplit : n = 2*(n/2)+1 := by omega
    refine ⟨n/2,?_⟩
    have hd := odd_input_double a (n/2) ha he
    rw [← hSplit] at hd
    omega
  · rintro ⟨j,rfl⟩
    exact odd_halt_section_family a j ha he

#print axioms odd_section_none_iff_haltingK
end BB6.Agent46
