import AffineHaltOneStep
import AffineParityDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

private theorem pow_four_lower_deep (m : Nat) : 3*m+4≤2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1)+2 = (2*n+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- The entire second halting family has right counter at least seven. -/
theorem second_halt_k_ge_seven (j m k : Nat)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) : 7≤k := by
  have hp := pow_four_lower_deep m
  have hfour : 4≤2^(2*m+2) := by omega
  have hl : 4*j ≤ 2^(2*m+2)*j := Nat.mul_le_mul_right j hfour
  have hr : 3*(3*m+4) ≤ 3*2^(2*m+2) := Nat.mul_le_mul_left 3 hp
  have hex : 2^(2*m+2)*(j+3) =
       2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  rw [hex] at hk
  omega

/-- The only potential multi-inverse-step second-family sector has a
forced first step and admits the exact all-depth 2-adic coordinate laws. -/
theorem second_halt_deep_sector (j m k : Nat)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hj : j%2=0) (hm : m%2=1) (hs : (j+m)%4=3) :
    4≤k ∧ k%4=2 ∧ 1≤oddDepth k ∧
    (let p := affineNormalize (2*j+3) k;
      p.1+2*p.2+4*oddDepth k = 2*j+3+2*k ∧
      2^(oddDepth k)*(p.2+2)=k+2) := by
  have ha : (2*j+3)%4=3 := by omega
  have hsum := second_halt_a_k_mod4 j m k hk
  have hres : k%4=2 := by omega
  have hbound : 4≤k := by
    have hbig := second_halt_k_ge_seven j m k hk
    omega
  have hd : 1≤oddDepth k := by
    rw [oddDepth, dif_pos (show 4≤k ∧ k%4=2 by omega)]
    omega
  refine ⟨hbound,hres,hd,?_⟩
  exact ⟨(normalize_three_depth_invariants (2*j+3) k ha).1,
    (normalize_three_depth_invariants (2*j+3) k ha).2.1⟩

#print axioms second_halt_k_ge_seven
#print axioms second_halt_deep_sector
end BB6.Agent15
