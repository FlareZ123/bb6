import EvenEvenInverse
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

private theorem odd_even_pow_two_even (n : Nat) (hn : 1≤n) :
    ∃ u : Nat, 2^n=2*u := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+1 := ⟨n-1,by omega⟩
  refine ⟨2^m,?_⟩
  rw [hm,Nat.pow_succ]
  omega

/-- A previously untreated even-right, odd-first region has no
    recursive-bounce parents. A direct affine return is its only source. -/
theorem section_oddeven_sum3_mod8_inverse (a k x y : Nat)
    (hy : 6≤y) (hx : x%2=1) (he : y%2=0)
    (hs : (x+y)%8=3)
    (h : secNext (a,k)=some (x,y)) :
    a=x+y-2 ∧ k=(y-2)/2 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        obtain ⟨n,hsum,_⟩ :=
          bounce_odd_output_invariants (2*k+1) 1 x y (by decide) hb
        have hm : x+y=8*(2^n) := by omega
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
            omega
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · have hb : (bounce 4 (2*k-3)).2=some (x,y) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hsum,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4 x y
                  (by decide) (by omega) hb
              have hm : x+y+1=16*(2^n) := by omega
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          constructor <;> omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion] using h
          by_cases haeven : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨n,hsum,_⟩ :=
              bounce_odd_output_invariants (2*k-a+3) (a-1)
                x y hodd hb
            have hm : x+y=2*(2^n*(a+2)) := by
              calc
                x+y=2^n*(2*(a-1)+6) := hsum
                _=2^n*(2*(a+2)) := by congr 1 <;> omega
                _=2*(2^n*(a+2)) := by ac_rfl
            omega
          · have heven : (a-1)%2=0 := by omega
            obtain ⟨n,hsum,hcost⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                x y heven (by omega) hb
            have hsum' : x+y+1=2^n*(2*(a-1)+8) := hsum
            have hcost' : 2*k+a+9+3*n=x+2*y+2 := by omega
            by_cases hn0 : n=0
            · subst n
              simp at hsum' hcost'
              omega
            · obtain ⟨u,hu⟩ := odd_even_pow_two_even n (by omega)
              obtain ⟨v,hv⟩ : ∃ v : Nat, 2*(a-1)+8=4*v :=
                ⟨(a+3)/2,by omega⟩
              have hdiv : x+y+1=8*(u*v) := by
                calc
                  x+y+1=2^n*(2*(a-1)+8) := hsum'
                  _=(2*u)*(4*v) := by rw [hu,hv]
                  _=(2*4)*(u*v) := by ac_rfl
                  _=8*(u*v) := by rfl
              omega

#print axioms section_oddeven_sum3_mod8_inverse
end BB6.Agent46
