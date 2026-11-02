import BounceHaltBasin
import Lean.Elab.Tactic.Omega
namespace BB6.Agent46
theorem odd_a_section_none_iff_level (a k : Nat) (ha : 3≤a) (he : a%2=1) :
    secNext (a,k)=none ↔
      (a<2*k ∧ ∃ n : Nat, 2*k-a+3=haltLevel (a-1) n) := by
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  by_cases hk0 : k=0
  · subst k
    simp [secNext,exactSection,ha0,ha1]
  · by_cases hd : 2*k≤a
    · have hnot : ¬a<2*k := by omega
      simp [secNext,exactSection,ha0,ha1,hk0,hd,hnot]
    · have hsmall : a<2*k := by omega
      have heven : (a-1)%2=0 := by omega
      have hc : 4≤2*k-a+3 := by omega
      have hrec := even_bounce_none_iff_level (2*k-a+3) (a-1) heven hc
      have hf : exactSection (a,k) =
          (a-1+(bounce (a-1) (2*k-a+3)).1,(bounce (a-1) (2*k-a+3)).2) := by
        simp [exactSection,ha0,ha1,hk0,hd]
      change (exactSection (a,k)).2=none ↔
        (a<2*k ∧ ∃ n : Nat, 2*k-a+3=haltLevel (a-1) n)
      rw [hf]
      simp only [hsmall,true_and]
      exact hrec
#print axioms odd_a_section_none_iff_level
end BB6.Agent46
