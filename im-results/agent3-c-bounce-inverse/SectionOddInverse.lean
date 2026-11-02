import BounceEvenExact
import BounceInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

private theorem bounce_odd_sum_even (c K x y : Nat)
    (hk : K%2=1) (hb : (bounce K c).2=some (x,y)) :
    (x+y)%2=0 := by
  obtain ⟨n,hs,_⟩ := bounce_odd_output_invariants c K x y hk hb
  have he : x+y=2*(2^n*(K+3)) := by
    calc
      x+y=2^n*(2*K+6) := hs
      _ = 2^n*(2*(K+3)) := by congr 1
      _ = 2*(2^n*(K+3)) := by ac_rfl
  omega

/-- Complete all-input source section inverse for the ENTIRE even-first,
    odd-second region with right counter at least five. This includes all
    exceptional source branches and every recursive bounce depth. -/
theorem section_even_odd_output_iff (a k x y : Nat)
    (hx : x%2=0) (ho : y%2=1) (hy : 5≤y) :
    secNext (a,k)=some (x,y) ↔
      (a=1 ∧ k=2 ∧ x=2 ∧ y=5) ∨
      (a=1 ∧ k=3 ∧ x=0 ∧ y=7) ∨
      (a=1 ∧ 4≤k ∧ ∃ n : Nat,
        x+y+1=2^n*16 ∧
        (2*k-3)+16+3*n=x+2*y+2) ∨
      (3≤a ∧ a%2=1 ∧ a<2*k ∧ ∃ n : Nat,
        x+y+1=2^n*(2*(a-1)+8) ∧
        (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
  constructor
  · intro h
    have hodd : (x+y)%2=1 := by omega
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,hk0,hk1] at h
          omega
        · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
          have hh := bounce_odd_sum_even (2*k+1) 1 x y (by decide) hb
          omega
    · by_cases ha1 : a=1
      · by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
          omega
        · by_cases hk1 : k=1
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
            omega
          · by_cases hk2 : k=2
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
              exact Or.inl ⟨ha1,hk2,by omega,by omega⟩
            · by_cases hk3 : k=3
              · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
                exact Or.inr (Or.inl ⟨ha1,hk3,by omega,by omega⟩)
              · have hb : (bounce 4 (2*k-3)).2=some (x,y) := by
                  simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
                obtain ⟨n,hs,hc⟩ := (bounce_even_output_exact 4 (2*k-3) x y (by decide) hy).mp hb
                have hs' : x+y+1=2^n*16 := by simpa using hs
                exact Or.inr (Or.inr (Or.inl ⟨ha1,by omega,⟨n,hs',by simpa using hc⟩⟩))
      · have ha2 : 2≤a := by omega
        by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
          omega
        · by_cases hlow : 2*k≤a
          · simp [secNext,exactSection,ha0,ha1,hk0,hlow] at h
            omega
          · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
              simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow] using h
            by_cases heven : a%2=0
            · have hkodd : (a-1)%2=1 := by omega
              have hh := bounce_odd_sum_even (2*k-a+3) (a-1) x y hkodd hb
              omega
            · have hkEven : (a-1)%2=0 := by omega
              obtain ⟨n,hs,hc⟩ := (bounce_even_output_exact (a-1) (2*k-a+3) x y hkEven hy).mp hb
              exact Or.inr (Or.inr (Or.inr ⟨by omega,by omega,by omega,⟨n,hs,hc⟩⟩))
  · intro h
    rcases h with h0 | h1 | h2 | h3
    · rcases h0 with ⟨rfl,rfl,rfl,rfl⟩
      decide
    · rcases h1 with ⟨rfl,rfl,rfl,rfl⟩
      decide
    · rcases h2 with ⟨rfl,hk,⟨n,hs,hc⟩⟩
      have hk0 : k≠0 := by omega
      have hk1 : k≠1 := by omega
      have hk2 : k≠2 := by omega
      have hk3 : k≠3 := by omega
      have hb : (bounce 4 (2*k-3)).2=some (x,y) := by
        apply (bounce_even_output_exact 4 (2*k-3) x y (by decide) hy).mpr
        refine ⟨n, ?_, ?_⟩
        · simpa using hs
        · simpa using hc
      simpa [secNext,exactSection,hk0,hk1,hk2,hk3] using hb
    · rcases h3 with ⟨ha,haOdd,hhigh,⟨n,hs,hc⟩⟩
      have ha0 : a≠0 := by omega
      have ha1 : a≠1 := by omega
      have hk0 : k≠0 := by omega
      have hlow : ¬2*k≤a := by omega
      have he : (a-1)%2=0 := by omega
      have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
        exact (bounce_even_output_exact (a-1) (2*k-a+3) x y he hy).mpr ⟨n,hs,hc⟩
      simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow] using hb

#print axioms section_even_odd_output_iff
end BB6.Agent46
