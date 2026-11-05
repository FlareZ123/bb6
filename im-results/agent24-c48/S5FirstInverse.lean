import EvenEvenInverse
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

private theorem s5_pow_four (n : Nat) (hn : 2≤n) : ∃ u : Nat, 2^n=4*u := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+2 := ⟨n-2,by omega⟩
  refine ⟨2^m,?_⟩
  rw [hm,Nat.pow_add]
  simp only [show (2:Nat)^2=4 by decide]
  omega

/-- The odd-odd valuation-three target has one exact predecessor,
    uniformly across all q and every bounce recursion depth. -/
theorem s5_first_inverse (q a k : Nat)
    (h : secNext (a,k)=some (17792*q+1379,7488*q+581)) :
    a=12640*q+978 ∧ k=10064*q+778 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2 =
            some (17792*q+1379,7488*q+581) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        obtain ⟨n,hsum,_⟩ :=
          bounce_odd_output_invariants (2*k+1) 1
            (17792*q+1379) (7488*q+581) (by decide) hb
        have hsum' : 25280*q+1960=8*(2^n) := by omega
        by_cases hn0 : n=0
        · subst n
          simp at hsum'
          omega
        · obtain ⟨u,hu⟩ := pow_two_even_new n (by omega)
          have hdiv : 25280*q+1960=16*u := by
            calc
              25280*q+1960=8*(2^n) := hsum'
              _=8*(2*u) := by rw [hu]
              _=16*u := by omega
          omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · have hb : (bounce 4 (2*k-3)).2 =
                  some (17792*q+1379,7488*q+581) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hsum,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4
                  (17792*q+1379) (7488*q+581) (by decide) (by omega) hb
              have hm : 25280*q+1961=16*(2^n) := by omega
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hreg : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hreg] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2 =
              some (17792*q+1379,7488*q+581) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hreg] using h
          by_cases haEven : a%2=0
          · have hkOdd : (a-1)%2=1 := by omega
            obtain ⟨n,hsum,hcost⟩ :=
              bounce_odd_output_invariants (2*k-a+3) (a-1)
                (17792*q+1379) (7488*q+581) hkOdd hb
            have hsum' : 25280*q+1960=2^n*(2*(a-1)+6) := by omega
            have hcost' : 32768*q+2541=2*k+a+7+3*n := by omega
            have hpar : n%2=0 := by omega
            by_cases hn0 : n=0
            · subst n
              simp at hsum' hcost'
              constructor <;> omega
            · obtain ⟨u,hu⟩ := s5_pow_four n (by omega)
              obtain ⟨v,hv⟩ : ∃ v : Nat, 2*(a-1)+6=4*v :=
                ⟨a/2+1,by omega⟩
              have hdiv : 25280*q+1960=16*(u*v) := by
                calc
                  25280*q+1960=2^n*(2*(a-1)+6) := hsum'
                  _=(4*u)*(4*v) := by rw [hu,hv]
                  _=16*(u*v) := by ring
              omega
          · have hkEven : (a-1)%2=0 := by omega
            obtain ⟨n,hsum,_⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                (17792*q+1379) (7488*q+581) hkEven (by omega) hb
            have hm : 25280*q+1961=2*(2^n*(a+3)) := by
              calc
                25280*q+1961=2^n*(2*(a-1)+8) := by omega
                _=2^n*(2*(a+3)) := by congr 1 <;> omega
                _=2*(2^n*(a+3)) := by ac_rfl
            omega

#print axioms s5_first_inverse
end BB6.Agent46
