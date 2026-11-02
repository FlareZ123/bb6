import AffineParityDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- The exact terminal inverse depth for any right counter with
    k+2=2^(d+1)*(2*q+1), q>0. This arbitrary-depth identity generalizes
    the formerly analyzed special case with odd part 3 modulo 4. -/
theorem oddDepth_odd_term (d q : Nat) (hq : 1≤q) :
    oddDepth (2^(d+1)*(2*q+1)-2) = d := by
  induction d with
  | zero =>
      have he : 2^(0+1)*(2*q+1)-2=4*q := by omega
      rw [he,oddDepth,dif_neg (by omega : ¬(4≤4*q ∧ (4*q)%4=2))]
  | succ d ih =>
      have hp : 2^((d+1)+1)=2*(2^(d+1)) := by
        rw [Nat.pow_succ]
        omega
      have hp4 : 2^((d+1)+1)=4*2^d := by
        have he : (d+1)+1=d+2 := by omega
        rw [he, Nat.pow_add]
        rw [show (2:Nat)^2=4 by decide]
        omega
      have hW : 3 ≤ 2^d*(2*q+1) := by
        have hQ : 3≤2*q+1 := by omega
        have hh : 2*q+1 ≤ 2^d*(2*q+1) :=
          Nat.le_mul_of_pos_left (2*q+1) (Nat.pow_pos (by decide))
        omega
      have hg : 4≤2^((d+1)+1)*(2*q+1)-2 ∧
          (2^((d+1)+1)*(2*q+1)-2)%4=2 := by
        rw [hp4]
        have he : (4*2^d)*(2*q+1)=4*(2^d*(2*q+1)) := by ac_rfl
        rw [he]
        omega
      rw [oddDepth,dif_pos hg]
      have hs : (2^((d+1)+1)*(2*q+1)-2-2)/2 =
          2^(d+1)*(2*q+1)-2 := by
        rw [hp, Nat.mul_assoc]
        have hB : 0 < 2^(d+1)*(2*q+1) :=
          Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
        omega
      rw [hs,ih]
      omega

#print axioms oddDepth_odd_term
end BB6.Agent11
