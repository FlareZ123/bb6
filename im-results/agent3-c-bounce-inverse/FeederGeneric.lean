import FastSectionDef
import BounceInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- A successful even-middle bounce cannot output an even coordinate sum
    when the second coordinate is at least four. -/
private theorem feeder_even_sum_impossible (c K x y : Nat)
    (hk : K%2=0) (hy : 4≤y)
    (hb : (bounce K c).2=some (x,y)) (hs : (x+y)%2=0) : False := by
  obtain ⟨n, hsum, _⟩ := bounce_even_output_invariants c K x y hk hy hb
  have he : x+y+1=2*(2^n*(K+4)) := by
    calc
      x+y+1=2^n*(2*K+8) := hsum
      _ = 2^n*(2*(K+4)) := by congr 1
      _ = 2*(2^n*(K+4)) := by ac_rfl
  omega

/-- Odd recursive bounce outputs in the family (16t+3,8t+1), t>0,
    have a unique original middle counter and original high counter.
    Crucially this statement covers every recursion depth. -/
private theorem feeder_odd_input (t K c : Nat) (ht : 1≤t)
    (hk : K%2=1) (hb : (bounce K c).2=some (16*t+3,8*t+1)) :
    K=12*t-1 ∧ c=8*t+1 := by
  obtain ⟨n,hsum,hcost⟩ :=
    bounce_odd_output_invariants c K (16*t+3) (8*t+1) hk hb
  have hs : 24*t+4=2^n*(2*K+6) := by omega
  have hc : c+(2*K+6)+3*n=32*t+5 := by omega
  have hf : ∃ z : Nat, 2*K+6=4*z := by
    refine ⟨(K+3)/2,?_⟩
    omega
  have hn : n=0 := by
    by_cases hzero : n=0
    · exact hzero
    have hp2 : 2 ∣ 2^n := by
      change 2^1 ∣ 2^n
      exact Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨u,hu⟩ := hp2
    obtain ⟨z,hz⟩ := hf
    have hdiv : 24*t+4=8*(u*z) := by
      calc
        24*t+4=2^n*(2*K+6) := hs
        _ = (2*u)*(4*z) := by rw [hu,hz]
        _ = (2*4)*(u*z) := by ac_rfl
        _ = 8*(u*z) := by rfl
    omega
  rw [hn] at hs hc
  simp at hs hc
  omega

/-- Every possible source-section preimage of the complete infinite
    four-j-plus-one feeder has one universal affine expression. -/
theorem feeder_generic_only_parent (t a k : Nat) (ht : 1≤t)
    (h : secNext (a,k)=some (16*t+3,8*t+1)) :
    a=12*t ∧ k=10*t-1 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (16*t+3,8*t+1) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have hi := feeder_odd_input t 1 (2*k+1) ht (by decide) hb
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
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · have hb : (bounce 4 (2*k-3)).2=some (16*t+3,8*t+1) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              exact False.elim (feeder_even_sum_impossible _ _ _ _ (by decide) (by omega) hb (by omega))
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (16*t+3,8*t+1) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          by_cases heven : (a-1)%2=0
          · exact False.elim (feeder_even_sum_impossible _ _ _ _ heven (by omega) hb (by omega))
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨hbK,hbC⟩ := feeder_odd_input t (a-1) (2*k-a+3) ht hodd hb
            omega

/-- The affine candidate is always a *real* source-section predecessor.
    Thus the necessary classification is an exact iff, not an overapproximation. -/
private theorem feeder_generic_true_edge (t : Nat) (ht : 1≤t) :
    secNext (12*t,10*t-1)=some (16*t+3,8*t+1) := by
  have h0 : 12*t≠0 := by omega
  have h1 : 12*t≠1 := by omega
  have hk : 10*t-1≠0 := by omega
  have hreg : ¬(2*(10*t-1)≤12*t) := by omega
  simp only [secNext,exactSection,if_neg h0,if_neg h1,
    if_neg hk,if_neg hreg]
  have hK : 12*t-1=12*t-1 := rfl
  have hC : 2*(10*t-1)-12*t+3=8*t+1 := by omega
  rw [hC]
  rw [bounce]
  have hlow : ¬(8*t+1<4) := by omega
  have hodd : (12*t-1)%2=1 := by omega
  have hsmall : 8*t+1≤2*(12*t-1)+6 := by omega
  simp only [hlow,ite_false,hodd,ite_true,hsmall,Option.some.injEq,
    Prod.mk.injEq]
  trace_state
  omega

/-- Uniform exact inverse for the complete j=4t+1 feeder, t>=1.
    This subsumes special t=8(16q+4), 8(16q+7) predecessor analyses. -/
theorem feeder_generic_iff (t a k : Nat) (ht : 1≤t) :
    secNext (a,k)=some (16*t+3,8*t+1) ↔ a=12*t ∧ k=10*t-1 := by
  constructor
  · exact feeder_generic_only_parent t a k ht
  · rintro ⟨rfl,rfl⟩
    exact feeder_generic_true_edge t ht

#print axioms feeder_generic_only_parent
#print axioms feeder_generic_iff
end BB6.Agent46
