import FastSectionDef
import SectionGate
import Lean.Elab.Tactic.Omega

namespace BB6.Agent49
open BB6.Agent46 (bounce secNext exactSection)

theorem section_small_source (a k : Nat) (ha : 2≤a) (hs : a<2*k) :
    secNext (a,k)=(bounce (a-1) (2*k-a+3)).2 := by
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hdom : ¬2*k≤a := by omega
  simp [secNext,exactSection,ha0,ha1,hk0,hdom]

theorem section_small_power_gate (a k : Nat) (ha : 2≤a) (hs : a<2*k) :
    (secNext (a,k)=none ↔
      a%2=1 ∧ ∃ n : Nat, 2*k+a+4+3*n=(a+3)*2^(n+1)) := by
  rw [section_small_source a k ha hs]
  exact small_section_bounce_gate a k ha hs

theorem section_even_small_survives (a k : Nat)
    (ha : 2≤a) (he : a%2=0) (hs : a<2*k) :
    secNext (a,k) ≠ none := by
  intro hh
  have hcrit := (section_small_power_gate a k ha hs).mp hh
  omega

theorem section_one_source (k : Nat) (hk : 4≤k) :
    secNext (1,k)=(bounce 4 (2*k-3)).2 := by
  have hne0 : k≠0 := by omega
  have hne1 : k≠1 := by omega
  have hne2 : k≠2 := by omega
  have hne3 : k≠3 := by omega
  simp [secNext,exactSection,hne0,hne1,hne2,hne3]

theorem section_one_power_gate (k : Nat) (hk : 4≤k) :
    (secNext (1,k)=none ↔ ∃ n : Nat,
       2*k+8+3*n=8*2^(n+1)) := by
  have hc : 4≤2*k-3 := by omega
  rw [section_one_source k hk,bounce_power_criterion 4 (2*k-3) hc]
  simp only [show 4%2=0 by decide,true_and]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    simpa only [show 4+4=8 by omega] using
      (show 2*k+8+3*n=8*2^(n+1) by omega)
  · rintro ⟨n,hn⟩
    exact ⟨n,by omega⟩

def SectionGate (a k : Nat) : Prop :=
  (a=0 ∧ k=0) ∨
  (a=1 ∧ 4≤k ∧ ∃ n : Nat, 2*k+8+3*n=8*2^(n+1)) ∨
  (2≤a ∧ a<2*k ∧ a%2=1 ∧
    ∃ n : Nat, 2*k+a+4+3*n=(a+3)*2^(n+1))

theorem source_section_gate_iff (a k : Nat) :
    (secNext (a,k)=none ↔ SectionGate a k) := by
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · subst k; simp [secNext, exactSection, SectionGate]
    · by_cases hk1 : k=1
      · subst k; simp [secNext, exactSection, SectionGate]
      · have hsec : secNext (0,k)=(bounce 1 (2*k+1)).2 := by
          simp [secNext,exactSection,hk0,hk1]
        have hn := bounce_odd_not_none (2*k+1) 1 (by decide) (by omega)
        rw [hsec]
        simp [SectionGate,hk0,hn]
  · by_cases ha1 : a=1
    · subst a
      by_cases hk4 : 4≤k
      · rw [section_one_power_gate k hk4]
        simp [SectionGate,hk4]
      · have hk3 : k≤3 := by omega
        have hcases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
        rcases hcases with h0 | h1 | h2 | h3
        · subst k; simp [secNext, exactSection, SectionGate]
        · subst k; simp [secNext, exactSection, SectionGate]
        · subst k; simp [secNext, exactSection, SectionGate]
        · subst k; simp [secNext, exactSection, SectionGate]
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · subst k
        simp [secNext,exactSection,ha0,ha1,SectionGate]
      · by_cases hd : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hd,SectionGate]
          intro _ hsmall
          omega
        · have hs : a<2*k := by omega
          rw [section_small_power_gate a k ha2 hs]
          simp [SectionGate,ha0,ha1,ha2,hs]

#print axioms source_section_gate_iff
#print axioms section_small_source
#print axioms section_small_power_gate
#print axioms section_even_small_survives
end BB6.Agent49
