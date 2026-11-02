import FastSectionHalting
import Lean.Elab.Tactic.Omega
namespace BB6.Agent46
theorem odd_bounce_survives (c : Nat) : ∀ k, k%2=1 → 4≤c →
    ∃ p : Nat × Nat, (bounce k c).2=some p := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k hk hc
    rw [bounce.eq_1]
    have hnot : ¬c<4 := by omega
    simp only [hnot,ite_false,hk,ite_true]
    by_cases hs : c≤2*k+6
    · simp only [hs,ite_true]
      exact ⟨(2*k+6-c,c),rfl⟩
    · simp only [hs,ite_false]
      have hlarge : 2*k+6<c := by omega
      have hcsmall : 4≤c-(2*k+3) := by omega
      have hlt : c-(2*k+3)<c := Nat.sub_lt (by omega) (by omega)
      have hko : (2*k+3)%2=1 := by omega
      obtain ⟨p,hp⟩ := ih (c-(2*k+3)) hlt (2*k+3) hko hcsmall
      exact ⟨p,hp⟩

theorem even_a_section_survives (a k : Nat) (ha : 2≤a) (he : a%2=0) :
    ∃ p : Nat × Nat, secNext (a,k)=some p := by
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  by_cases hk0 : k=0
  · subst k
    refine ⟨(a-2,2),?_⟩
    simp [secNext,exactSection,ha0,ha1]
  · by_cases hd : 2*k≤a
    · refine ⟨(a-2*k,2*k+2),?_⟩
      simp [secNext,exactSection,ha0,ha1,hk0,hd]
    · have hlow : a<2*k := by omega
      have hko : (a-1)%2=1 := by omega
      have hc : 4≤2*k-a+3 := by omega
      obtain ⟨p,hp⟩ := odd_bounce_survives (2*k-a+3) (a-1) hko hc
      refine ⟨p,?_⟩
      simp [secNext,exactSection,ha0,ha1,hk0,hd,hp]

#print axioms odd_bounce_survives
#print axioms even_a_section_survives
end BB6.Agent46
