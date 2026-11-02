import EvenTargetForward
import GeneralHighInverse
import BounceInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

private theorem odd_bounce_even_sum (c K x y : Nat) (hk : K%2=1)
    (hb : (bounce K c).2=some (x,y)) : (x+y)%2=0 := by
  obtain ⟨n,hs,_⟩ := bounce_odd_output_invariants c K x y hk hb
  have he : x+y=2*(2^n*(K+3)) := by
    calc
      x+y=2^n*(2*K+6) := hs
      _ = 2^n*(2*(K+3)) := by congr 1
      _ = 2*(2^n*(K+3)) := by ac_rfl
  omega

private theorem pow2_nonzero_mod11 (n : Nat) : 2^n%11≠0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

private theorem pow4_cancel_mod11 (r x : Nat)
    (h : (4^r*x)%11=0) : x%11=0 := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    rw [Nat.pow_succ] at h
    have hstep : (4*(4^r*x))%11=0 := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    have hprev : (4^r*x)%11=0 := by omega
    exact ih hprev

private theorem high_section_param (t a k : Nat)
    (ht : 1≤t) (ha : 3≤a) (hodd : a%2=1) (hhigh : a<2*k)
    (h : secNext (a,k)=some (12*t,10*t-1)) :
    ∃ r u : Nat, 1≤u ∧ t=2*(4^r*u) ∧
      a=22*u-3 ∧ k=32*(4^r*u)-(11*u+3+3*r) := by
  obtain ⟨r,hpower,hcost⟩ :=
    target_high_inverse_power4 t a k ht ha hodd hhigh h
  have h11 : (4^r*(a+3))%11=0 := by omega
  have hdiv11 : (a+3)%11=0 := pow4_cancel_mod11 r (a+3) h11
  have hdiv2 : (a+3)%2=0 := by omega
  have hdiv22 : (a+3)%22=0 := by omega
  let u : Nat := (a+3)/22
  have hau : a+3=22*u := by dsimp [u]; omega
  have hu : 1≤u := by omega
  have hmu : 4^r*(a+3)=11*(2*(4^r*u)) := by
    calc
      4^r*(a+3)=4^r*(22*u) := by rw [hau]
      _ = 11*(2*(4^r*u)) := by
        rw [show (22:Nat)=11*2 by decide]
        ac_rfl
  have htEq : t=2*(4^r*u) := by omega
  have haEq : a=22*u-3 := by omega
  have hkEq : k=32*(4^r*u)-(11*u+3+3*r) := by omega
  exact ⟨r,u,hu,htEq,haEq,hkEq⟩

/-- COMPLETE source-specific inverse grammar for the whole odd-right target
    family, uniformly in t. Every parent is genuine (by EvenTargetForward).
    This theorem quantifies over all bounce recursion depths. -/
theorem universal_target_inverse_iff (t a k : Nat) (ht : 1≤t) :
    secNext (a,k)=some (12*t,10*t-1) ↔
      ∃ r u : Nat, 1≤u ∧ t=2*(4^r*u) ∧
        a=22*u-3 ∧ k=32*(4^r*u)-(11*u+3+3*r) := by
  constructor
  · intro h
    have hsumodd : (12*t+(10*t-1))%2=1 := by omega
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,hk0,hk1] at h
          omega
        · have hb : (bounce 1 (2*k+1)).2 = some (12*t,10*t-1) := by
            simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
          have he := odd_bounce_even_sum (2*k+1) 1 (12*t) (10*t-1) (by decide) hb
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
              · have hb : (bounce 4 (2*k-3)).2=some (12*t,10*t-1) := by
                  simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
                obtain ⟨n,hs,_⟩ := bounce_even_output_invariants
                    (2*k-3) 4 (12*t) (10*t-1) (by decide) (by omega) hb
                have hsum : 11*t=8*(2^n) := by omega
                have hn := pow2_nonzero_mod11 n
                have hc : (8*(2^n))%11=0 := by omega
                omega
      · have ha2 : 2≤a := by omega
        by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
          omega
        · by_cases hlow : 2*k≤a
          · simp [secNext,exactSection,ha0,ha1,hk0,hlow] at h
            omega
          · have hb : (bounce (a-1) (2*k-a+3)).2=some (12*t,10*t-1) := by
              simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow] using h
            by_cases heven : a%2=0
            · have hodd : (a-1)%2=1 := by omega
              have hh := odd_bounce_even_sum (2*k-a+3) (a-1)
                  (12*t) (10*t-1) hodd hb
              omega
            · exact high_section_param t a k ht (by omega) (by omega) (by omega) h
  · rintro ⟨r,u,hu,htEq,haEq,hkEq⟩
    subst t
    subst a
    subst k
    have h := general_even_inverse_edge r u hu
    have hx : 24*(4^r*u)=12*(2*(4^r*u)) := by omega
    have hy : 20*(4^r*u)-1=10*(2*(4^r*u))-1 := by omega
    simpa only [hx,hy] using h

#print axioms universal_target_inverse_iff
end BB6.Agent46
