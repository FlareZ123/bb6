import AffineTarget56
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

private theorem even_bounce_odd_sum (k c x y : Nat) (hk:k%2=0)
    (hy:4≤y) (h:(bounce k c).2=some (x,y)) : (x+y)%2=1 := by
  obtain ⟨n,hsum,_⟩ := bounce_even_output_invariants c k x y hk hy h
  have hf : 2*k+8=2*(k+4) := by omega
  have he : x+y+1=2*(2^n*(k+4)) := by
    calc
      x+y+1 = 2^n*(2*k+8) := hsum
      _ = 2^n*(2*(k+4)) := by rw [hf]
      _ = 2*(2^n*(k+4)) := by ac_rfl
  omega

private theorem odd_feeder_bounce_inverse (q K c : Nat) (hk:K%2=1)
    (h:(bounce K c).2=some (2048*q+899,1024*q+449)) :
    K=1536*q+671 ∧ c=1024*q+449 := by
  obtain ⟨n,hsum,hcost⟩ :=
    bounce_odd_output_invariants c K (2048*q+899) (1024*q+449) hk h
  have hsum' : 3072*q+1348 = 2^n*(2*K+6) := by omega
  have hcost' : c+(2*K+6)+3*n=4096*q+1797 := by omega
  have hfactor : ∃ z, 2*K+6=4*z := by
    refine ⟨(K+3)/2,?_⟩
    omega
  have hn0 : n=0 := by
    by_cases hh : n=0
    · exact hh
    have hp2 : 2 ∣ 2^n := by
      change 2^1 ∣ 2^n
      exact Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨u,hu⟩ := hp2
    obtain ⟨z,hz⟩ := hfactor
    have hdiv : 3072*q+1348=8*(u*z) := by
      calc
        3072*q+1348 = 2^n*(2*K+6) := hsum'
        _ = (2*u)*(4*z) := by rw [hu,hz]
        _ = (2*4)*(u*z) := by ac_rfl
        _ = 8*(u*z) := by rfl
    omega
  rw [hn0] at hsum' hcost'
  simp at hsum' hcost'
  omega

/-- Every predecessor of the entire second-stage feeder family is the
    same unique affine state, uniformly at every natural parameter. -/
theorem feeder_inverse56 (q a k : Nat)
    (h : secNext (a,k)=some (2048*q+899,1024*q+449)) :
    a=1536*q+672 ∧ k=1280*q+559 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (2048*q+899,1024*q+449) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have hh := odd_feeder_bounce_inverse q 1 (2*k+1) (by decide) hb
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
            · have hb : (bounce 4 (2*k-3)).2=some (2048*q+899,1024*q+449) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              have he := even_bounce_odd_sum 4 (2*k-3) (2048*q+899) (1024*q+449)
                (by decide) (by omega) hb
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (2048*q+899,1024*q+449) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          by_cases he : (a-1)%2=0
          · have hh := even_bounce_odd_sum (a-1) (2*k-a+3) (2048*q+899)
                (1024*q+449) he (by omega) hb
            omega
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨ha,hc⟩ := odd_feeder_bounce_inverse q (a-1) (2*k-a+3) hodd hb
            omega

#print axioms odd_feeder_bounce_inverse
#print axioms feeder_inverse56
end BB6.Agent46
