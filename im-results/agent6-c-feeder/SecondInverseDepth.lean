import COneFiveDepth
import BounceEvenGrammar
import BounceOddGrammar
import Lean.Elab.Tactic.Omega

namespace BB6.Agent6
open BB6.Agent3 BB6.Agent46

#check BB6Agent38.bounce_odd_four_direct
#check BB6Agent38.blank_section_no_11
#check BB6Agent38.blank_section_no_33

/-- A source-independent exact inverse arithmetic certificate for every
    EvenBack grammar branch, including arbitrary recursion depth. -/
theorem evenBack_depth_cost (x y k c : Nat) (hy : 5≤y)
    (h : EvenBack x y k c) :
    ∃ n : Nat,
      x+y+1 = 2^n*(2*k+8) ∧
      c+(2*k+8)+3*n=x+2*y+2 := by
  induction h with
  | small k hk hx hyeq => omega
  | large k hk hylarge hbd hx =>
      refine ⟨0, ?_, ?_⟩
      · simp
        omega
      · omega
  | step k c hk hc h ih =>
      obtain ⟨n,hpow,hcost⟩ := ih
      refine ⟨n+1, ?_, ?_⟩
      · rw [Nat.pow_succ]
        have hfactor : 2*(2*k+4)+8 = 2*(2*k+8) := by omega
        calc
          x+y+1 = 2^n*(2*(2*k+8)) := by rw [← hfactor]; exact hpow
          _ = (2^n*2)*(2*k+8) := by rw [Nat.mul_assoc]
      · omega

/-- The specific 2-adic family has only two possible source parity classes
    at the beginning of its genuine even-bounce inverse grammar. -/
theorem even_back_target_restricted (q kin c a k : Nat)
    (hkn : kin%2=0) (hc : c%2=0)
    (h : EvenBack (24*(16*q+4)) (20*(16*q+4)-1) kin c)
    (ha : a=kin+1) (hrelation : c+a=2*k+3) :
    (a%4=1 ∧ k%4=1) ∨ (a%4=3 ∧ k%4=3) := by
  have hy : 5≤20*(16*q+4)-1 := by omega
  obtain ⟨n,hpow,hcost⟩ := evenBack_depth_cost _ _ _ _ hy h
  have hformula : 44*(16*q+4) = 2^n*(2*kin+8) := by omega
  have hcost2 : c+(2*kin+8)+3*n=64*(16*q+4) := by omega
  have hn2 : n≤2 := by
    by_cases hn : n≤2
    · exact hn
    have hp8 : 8 ∣ 2^n := by
      change 2^3 ∣ 2^n
      exact Nat.pow_dvd_pow 2 (by omega)
    have hk4 : 4 ∣ 2*kin+8 := by
      refine ⟨kin/2+2,?_⟩
      omega
    obtain ⟨u,hu⟩ := hp8
    obtain ⟨v,hv⟩ := hk4
    have hd32 : 32 ∣ 2^n*(2*kin+8) := by
      refine ⟨u*v,?_⟩
      rw [hu,hv]
      calc
        (8*u)*(4*v) = (8*4)*(u*v) := by ac_rfl
        _ = 32*(u*v) := by rfl
    have hmod : (44*(16*q+4))%32=0 := by
      rw [hformula]
      exact Nat.mod_eq_zero_of_dvd hd32
    omega
  have hneven : n%2=0 := by omega
  have hh : n=0 ∨ n=2 := by omega
  rcases hh with h0 | h2
  · rw [h0] at hformula hcost2
    simp at hformula
    left
    omega
  · rw [h2] at hformula hcost2
    have heq : (2:Nat)^2=4 := by decide
    rw [heq] at hformula
    right
    omega

#print axioms evenBack_depth_cost
#print axioms even_back_target_restricted

end BB6.Agent6
