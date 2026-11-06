import CMapBridge192
import HighZeroOdd
import HighZeroEven
import CZeroBridge

set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Agent41M192
open Agent38M192

private theorem low_small_k (a k c : Nat) (hk : k < 8)
    (hw : (k+c)%192 ≠ 11) : ¬ low a k c := by
  intro h
  dsimp [low] at h
  rcases h with ⟨_, _, hguard⟩
  rcases hguard with hlarge | hspecial
  · omega
  · exact hw hspecial.2.1

private theorem high_not_sum_one (a k c : Nat)
    (ht : (a+k)%192=1) : ¬ high a k c := by
  intro hh
  simp only [high] at hh
  rcases hh with h|h|h|h|h|h|h|h|h|h|h|h <;> omega

private theorem high_not_sum_four (a k c : Nat)
    (ht : (a+k)%192=4) : ¬ high a k c := by
  intro hh
  simp only [high] at hh
  rcases hh with h|h|h|h|h|h|h|h|h|h|h|h <;> omega

/-- Contrapositive one-step closure of the phase-sensitive M192 reverse core. -/
theorem backward_step (a k c a' k' c' : Nat)
    (h : nextC a k c = some (a',k',c'))
    (hb : bad a' k' c') : bad a k c := by
  by_cases hc1 : c=1
  · subst c
    simp [nextC] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact low_step1 a k hb
  by_cases hc2 : c=2
  · subst c
    simp [nextC] at h
  by_cases hc3 : c=3
  · subst c
    simp [nextC] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact low_step3 a k hb
  by_cases hc0 : c=0
  · subst c
    by_cases ha0 : a=0
    · subst a
      simp [nextC] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      have hfalse : ¬ bad 1 0 (2*k+2) := by
        by_cases hc : 2*k+2<8
        · simp only [bad, hc, ↓reduceIte]
          exact low_small_k 1 0 (2*k+2) (by omega) (by omega)
        · simp only [bad, hc, ↓reduceIte]
          exact high_not_sum_one 1 0 (2*k+2) (by simp)
      exact False.elim (hfalse hb)
    by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · subst k
        simp [nextC] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (bad_root_absent hb)
      · simp [nextC,ha0,hk0] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        have hfalse : ¬ bad 2 2 (2*k-1) := by
          by_cases hk5 : 5≤k
          · have hc : ¬(2*k-1<8) := by omega
            simp only [bad, hc, ↓reduceIte]
            exact high_not_sum_four 2 2 (2*k-1) (by simp)
          · have hrange : k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
            rcases hrange with h1|h2|h3|h4 <;> subst k <;> simp [bad,low,lowCore]
        exact False.elim (hfalse hb)
    · have ha2 : 2≤a := by omega
      simp [nextC,ha0,ha1] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      by_cases hk4 : 4≤k
      · have hhi : high (a-2) 1 (2*k+1) := by
          have hc : ¬(2*k+1<8) := by omega
          simpa only [bad,hc,↓reduceIte] using hb
        have hlow := czero_large_parent a k ha2 hk4 hhi
        simpa only [bad,show (0:Nat)<8 by omega,↓reduceIte] using hlow
      · have hsmall : k<4 := by omega
        have hfalse : ¬ bad (a-2) 1 (2*k+1) := by
          have hw : (1+(2*k+1))%192 ≠ 11 := by omega
          simp only [bad,show 2*k+1<8 by omega,↓reduceIte]
          exact low_small_k (a-2) 1 (2*k+1) (by decide) hw
        exact False.elim (hfalse hb)
  · have hc4 : 4≤c := by omega
    by_cases ha0 : a=0
    · subst a
      by_cases he : k%2=0
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        by_cases hc11 : 11≤c
        · exact False.elim (high_zero_even k c he (by omega) hb)
        · have hw : (2+(c-3))%192 ≠ 11 := by omega
          have hfalse : ¬ bad (2*k+2) 2 (c-3) := by
            simp only [bad,show c-3<8 by omega,↓reduceIte]
            exact low_small_k (2*k+2) 2 (c-3) (by decide) hw
          exact False.elim (hfalse hb)
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        have hk1 : k%2=1 := by omega
        by_cases hc8 : 8≤c
        · have hhi : high (2*k+3) 0 c := by
            simpa only [bad,show ¬(c<8) by omega,↓reduceIte] using hb
          have hnext := high_zero_odd k c hk1 hhi
          simpa only [bad,show ¬(c<8) by omega,↓reduceIte] using hnext
        · have hw : (0+c)%192 ≠ 11 := by omega
          exact False.elim (low_small_k (2*k+3) 0 c (by decide) hw hb)
    · have ha : 0<a := by omega
      by_cases hc7 : c≤7
      · have hlow : low (a-1) (k+1) (c-1) := by
          simpa only [bad,show c-1<8 by omega,↓reduceIte] using hb
        have hnext := low_step_mid a k c ha hc4 hc7 hlow
        simpa only [bad,show c<8 by omega,↓reduceIte] using hnext
      · by_cases hc8 : c=8
        · have hlow : low (a-1) (k+1) 7 := by
            simpa only [bad,show (7:Nat)<8 by omega,↓reduceIte] using hb
          have hnext := low7_to_high8 a k ha hlow
          simpa only [bad,show ¬(8:Nat)<8 by omega,↓reduceIte] using hnext
        · have hcgt : 8<c := by omega
          have hhi : high (a-1) (k+1) (c-1) := by
            simpa only [bad,show ¬(c-1<8) by omega,↓reduceIte] using hb
          have hnext := high_a_pos a k c ha hcgt hhi
          simpa only [bad,show ¬(c<8) by omega,↓reduceIte] using hnext

/-- No state in the reverse core is reachable from the authentic blank entry. -/
theorem source_blank_never_bad (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬ bad s.1 s.2.1 s.2.2 := by
  induction h with
  | init => exact bad_root_absent
  | next x y hx hstep ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨a',k',c'⟩
      intro hb
      have he : nextC a k c = some (a',k',c') := by
        rw [nextC_eq_CLine]
        exact hstep
      exact ih (backward_step a k c a' k' c' he hb)

/-- The entire `(9 mod 192, 67 mod 192, 0)` cylinder is blank-unreachable. -/
theorem source_no_9_67 (a k : Nat)
    (ha : a%192=9) (hk : k%192=67)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  exact (source_blank_never_bad (a,k,0) h) (bad_target a k ha hk)

/-- The second stopping equation has the claimed residue on this parameter cylinder. -/
theorem second_stop_residues (j m k : Nat)
    (hm : 2≤m) (hj : j%192=3) (hmod : m%64=39)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%192=9 ∧ k%192=67 := by
  have hp : 2^(2*m+2)%192=64 := by
    have hmul : ∀ n : Nat, (64*4^n)%192=64 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            (64*4^(n+1))%192 = ((64*4^n)%192 * 4)%192 := by
              rw [pow_succ, Nat.mul_mod]
              simp
            _ = 64 := by rw [ih]; simp
    have hexp : 2*m+2=6+2*(m-2) := by omega
    have hpow : 2^(2*m+2)=64*4^(m-2) := by
      rw [hexp, Nat.pow_add, Nat.pow_mul]
      simp
    rw [hpow]
    exact hmul (m-2)
  have hj3 : (j+3)%192=6 := by omega
  have hR : (2^(2*m+2)*(j+3))%192=0 := by
    rw [Nat.mul_mod, hp, hj3]
  have hL : (k+j+3*m+5)%192=0 := by rw [hstop]; exact hR
  constructor
  · omega
  · omega

/-- This infinite second-stopping parameter family is excluded from the true blank orbit. -/
theorem source_no_second_stop_family (j m k : Nat)
    (hm : 2≤m) (hj : j%192=3) (hmod : m%64=39)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (h : BB6CLine.Reach (2*j+3,k,0)) : False := by
  obtain ⟨ha,hk⟩ := second_stop_residues j m k hm hj hmod hstop
  exact source_no_9_67 (2*j+3) k ha hk h

#print axioms backward_step
#print axioms source_blank_never_bad
#print axioms source_no_9_67
#print axioms second_stop_residues
#print axioms source_no_second_stop_family
end Agent41M192
