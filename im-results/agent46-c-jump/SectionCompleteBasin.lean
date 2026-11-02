import OddSectionExponential
import Lean.Elab.Tactic.Omega
namespace BB6.Agent46

def SectionHaltTarget (a k : Nat) : Prop :=
    (a=0 ∧ k=0) ∨
    (a=1 ∧ 4≤k ∧ ∃ n : Nat, 2*k-3=haltLevel 4 n) ∨
    (3≤a ∧ a%2=1 ∧ a<2*k ∧ ∃ n : Nat, 2*k-a+3=haltLevel (a-1) n)

theorem section_none_iff_target (a k : Nat) :
    secNext (a,k)=none ↔ SectionHaltTarget a k := by
  unfold SectionHaltTarget
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · subst k
      simp [secNext,exactSection]
    · by_cases hk1 : k=1
      · subst k
        simp [secNext,exactSection]
      · have hk2 : 2≤k := by omega
        have hodd : 1%2=1 := by omega
        have hc : 4≤2*k+1 := by omega
        obtain ⟨p,hp⟩ := odd_bounce_survives (2*k+1) 1 hodd hc
        have hnon : secNext (0,k)≠none := by
          simp [secNext,exactSection,hk0,hk1,hp]
        simp [hnon,hk0]
  · by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · subst k
        simp [secNext,exactSection]
      · by_cases hk1 : k=1
        · subst k
          simp [secNext,exactSection]
        · by_cases hk2 : k=2
          · subst k
            simp [secNext,exactSection]
          · by_cases hk3 : k=3
            · subst k
              simp [secNext,exactSection]
            · have hk4 : 4≤k := by omega
              have hc : 4≤2*k-3 := by omega
              have hb := even_bounce_none_iff_level (2*k-3) 4 (by omega) hc
              have hred : secNext (1,k)=(bounce 4 (2*k-3)).2 := by
                simp [secNext,exactSection,hk0,hk1,hk2,hk3]
              rw [hred]
              simpa [hk4] using hb
    · by_cases he : a%2=0
      · have ha2 : 2≤a := by omega
        have ⟨p,hp⟩ := even_a_section_survives a k ha2 he
        have hn : secNext (a,k)≠none := by rw [hp]; exact Option.some_ne_none _
        simp [hn,ha0,ha1,he]
      · have ha3 : 3≤a := by omega
        have ho : a%2=1 := by omega
        rw [odd_a_section_none_iff_level a k ha3 ho]
        simp [ha0,ha1,ha3,ho]

#print axioms section_none_iff_target
end BB6.Agent46
