import OddDepthGeneric
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- At any arbitrary forced-affine inverse depth, the normalized
    right counter is exactly four times the remaining odd-part parameter.
    The weighted source mass then determines its normalized residue. -/
theorem odd_term_normalized_residue (a d q : Nat)
    (ha : a%4=3) (hq : 1≤q)
    (hMass : (a+2*(2^(d+1)*(2*q+1)-2))%32=23) :
    let p := affineNormalize a (2^(d+1)*(2*q+1)-2)
    p.2 = 4*q ∧ (p.1+8*q+4*d)%32=23 := by
  let k := 2^(d+1)*(2*q+1)-2
  let p := affineNormalize a k
  have hdepth : oddDepth k=d := oddDepth_odd_term d q hq
  obtain ⟨hm,hs,_⟩ := normalize_three_depth_invariants a k ha
  change p.1+2*p.2+4*oddDepth k=a+2*k at hm
  change 2^(oddDepth k)*(p.2+2)=k+2 at hs
  have hfactor : k+2=2^d*(4*q+2) := by
    dsimp [k]
    have hp : 2^(d+1)=2^d*2 := Nat.pow_succ 2 d
    rw [hp]
    have he : 2*(2*q+1)=4*q+2 := by omega
    have hraw : 2^d * 2 * (2*q+1) = 2^d*(4*q+2) := by
      rw [Nat.mul_assoc,he]
    rw [hraw]
    have hh : 2 ≤ 2^d*(4*q+2) := by
      calc
        2 ≤ 4*q+2 := by omega
        _ ≤ 2^d*(4*q+2) :=
          Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
    omega
  have hright : p.2+2 = 4*q+2 := by
    have ht : 2^d*(p.2+2) = 2^d*(4*q+2) := by
      rw [hdepth] at hs
      exact hs.trans hfactor
    exact Nat.mul_left_cancel (Nat.pow_pos (by decide)) ht
  have hpeq : p.2=4*q := by omega
  have hmass : (a+2*k)%32=23 := by
    change (a+2*k)%32=23 at hMass
    exact hMass
  constructor
  · exact hpeq
  · change (p.1+8*q+4*d)%32=23
    rw [hdepth,hpeq] at hm
    have hlink : p.1+8*q+4*d=a+2*k := by omega
    rw [hlink]
    exact hmass

#print axioms odd_term_normalized_residue
end BB6.Agent11
