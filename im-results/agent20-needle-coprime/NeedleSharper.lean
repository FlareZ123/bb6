import NeedleCubicBound
import Lean.Elab.Tactic.Omega

namespace NeedleSharper
open NeedleInverse

private theorem exponential_dominates (n : Nat) :
    4*(n+10)+50 ≤ (2:Nat)^(n+8) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hp : (2:Nat)^(n+1+8)=2*2^(n+8) := by
      rw [show n+1+8=(n+8)+1 by omega, Nat.pow_succ']
    rw [hp]
    have hz : 0 < (2:Nat)^(n+8) := Nat.pow_pos (by decide)
    omega

private theorem dominance (v : Nat) (hv : 10 ≤ v) :
    4*v+50 ≤ (2:Nat)^(v-2) := by
  have hl : 4*v+50 = 4*((v-10)+10)+50 := by omega
  have hr : v-2=(v-10)+8 := by omega
  rw [hl,hr]
  exact exponential_dominates (v-10)

private theorem small_middle (q v s : Nat)
    (hv : v ≤ 9) (hs : 1 ≤ s)
    (hlow : v ≤ s+2) (hhi : s ≤ v+2)
    (h : equation q v (2*v+s)) : False := by
  have hm := NeedleCubicBound.terminal_modular_gate q v s h
  have heqv : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 ∨ v=5 ∨ v=6 ∨ v=7 ∨ v=8 ∨ v=9 := by omega
  rcases heqv with hv0 | hv1 | hv2 | hv3 | hv4 | hv5 | hv6 | hv7 | hv8 | hv9
  all_goals subst v
  all_goals have heqs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 ∨ s=6 ∨ s=7 ∨ s=8 ∨ s=9 ∨ s=10 ∨ s=11 := by omega
  all_goals rcases heqs with hs0 | hs1 | hs2 | hs3 | hs4 | hs5 | hs6 | hs7 | hs8 | hs9 | hs10 | hs11
  all_goals subst s
  all_goals simp [den] at hm <;> omega

private theorem large_middle (q v s : Nat)
    (hv : 10 ≤ v) (_hs : 1 ≤ s)
    (hlow : v ≤ s+2) (hhi : s ≤ v+2)
    (h : equation q v (2*v+s)) : False := by
  let z := (2:Nat)^(v-2)
  have hb : 4*v+50 ≤ z := dominance v hv
  have hp : (2:Nat)^v = 4*z := by
    have hV : v=(v-2)+2 := by omega
    rw [hV,Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    change 2^(v-2)*4=4*2^(v-2)
    omega
  have hD : den v = 8*z+3 := by
    simp only [den,Nat.pow_succ']
    rw [hp]
    omega
  have hm := NeedleCubicBound.terminal_modular_gate q v s h
  have hl : (4*v)%(den v)=4*v :=
    Nat.mod_eq_of_lt (NeedleCubicBound.four_v_lt_den v)
  rw [hl] at hm
  let i := s-(v-2)
  have he : s=(v-2)+i := by dsimp [i]; omega
  have hi : i≤4 := by dsimp [i]; omega
  have hsPow : (2:Nat)^s=z*2^i := by
    rw [he,Nat.pow_add]
  have hicases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases hicases with h0 | h1 | h2 | h3 | h4
  · have hPow : (2:Nat)^s = 1*z := by
      rw [hsPow, h0]
      all_goals omega
    have hN : 9*2^s+6 = 9*(1*z)+6 := by rw [hPow]
    have hR : z+3 < den v := by rw [hD]; omega
    have hEq : 9*(1*z)+6 = (z+3)+(den v)*1 := by
      rw [hD]
      omega
    have hMod : (9*2^s+6)%(den v) = z+3 := by
      rw [hN,hEq,Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hR
    rw [hMod] at hm
    omega
  · have hPow : (2:Nat)^s = 2*z := by
      rw [hsPow, h1]
      all_goals omega
    have hN : 9*2^s+6 = 9*(2*z)+6 := by rw [hPow]
    have hR : 2*z < den v := by rw [hD]; omega
    have hEq : 9*(2*z)+6 = (2*z)+(den v)*2 := by
      rw [hD]
      omega
    have hMod : (9*2^s+6)%(den v) = 2*z := by
      rw [hN,hEq,Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hR
    rw [hMod] at hm
    omega
  · have hPow : (2:Nat)^s = 4*z := by
      rw [hsPow, h2]
      all_goals omega
    have hN : 9*2^s+6 = 9*(4*z)+6 := by rw [hPow]
    have hR : 4*z-6 < den v := by rw [hD]; omega
    have hEq : 9*(4*z)+6 = (4*z-6)+(den v)*4 := by
      rw [hD]
      omega
    have hMod : (9*2^s+6)%(den v) = 4*z-6 := by
      rw [hN,hEq,Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hR
    rw [hMod] at hm
    omega
  · have hPow : (2:Nat)^s = 8*z := by
      rw [hsPow, h3]
      all_goals omega
    have hN : 9*2^s+6 = 9*(8*z)+6 := by rw [hPow]
    have hR : 8*z-18 < den v := by rw [hD]; omega
    have hEq : 9*(8*z)+6 = (8*z-18)+(den v)*8 := by
      rw [hD]
      omega
    have hMod : (9*2^s+6)%(den v) = 8*z-18 := by
      rw [hN,hEq,Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hR
    rw [hMod] at hm
    omega
  · have hPow : (2:Nat)^s = 16*z := by
      rw [hsPow, h4]
      all_goals omega
    have hN : 9*2^s+6 = 9*(16*z)+6 := by rw [hPow]
    have hR : 8*z-45 < den v := by rw [hD]; omega
    have hEq : 9*(16*z)+6 = (8*z-45)+(den v)*17 := by
      rw [hD]
      omega
    have hMod : (9*2^s+6)%(den v) = 8*z-45 := by
      rw [hN,hEq,Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hR
    rw [hMod] at hm
    omega

/-- Apart from one explicitly solved predecessor, terminal exponent K must
be at least 3*v+3, and this sharp threshold occurs at valuations 2 and 3. -/
theorem sharper_valuation_bound (q v K : Nat)
    (h : equation q v K) :
    (q=61 ∧ v=6 ∧ K=13) ∨ 3*v+3 ≤ K := by
  have hb := NeedleCubicBound.cubic_valuation_bound q v K h
  rcases hb with hspecial | hlo
  · exact Or.inl hspecial
  · by_cases hstrong : 3*v+3 ≤ K
    · exact Or.inr hstrong
    · have hh := NeedleValHalf.predecessor_valuation_strict q v K h
      let s := K-2*v
      have hK : K=2*v+s := by dsimp [s]; omega
      have hs : 1 ≤ s := by dsimp [s]; omega
      have hlow : v ≤ s+2 := by dsimp [s]; omega
      have hhi : s ≤ v+2 := by dsimp [s]; omega
      have h' : equation q v (2*v+s) := by simpa only [←hK] using h
      have hf : False := by
        by_cases hv : v ≤ 9
        · exact small_middle q v s hv hs hlow hhi h'
        · exact large_middle q v s (by omega) hs hlow hhi h'
      exact False.elim hf

theorem threshold_attained_v2 : equation 45 2 9 := by decide
theorem threshold_attained_v3 : equation 214 3 12 := by decide

#print axioms sharper_valuation_bound
#print axioms threshold_attained_v2
#print axioms threshold_attained_v3
#print axioms large_middle
#print axioms small_middle
#print axioms dominance
end NeedleSharper
