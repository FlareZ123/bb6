import DeepLowGate
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- The forced-affine inversion depth is exactly twice the exponent
    parameter for every shifted odd part congruent to three modulo four.
    This handles unbounded depths by induction over a natural index. -/
theorem depth_pow_oddpart_three (r q : Nat) :
    oddDepth (2^(2*r+1)*(4*q+3)-2)=2*r := by
  induction r with
  | zero =>
      have hk0 : ¬(4≤2^(2*0+1)*(4*q+3)-2 ∧
          (2^(2*0+1)*(4*q+3)-2)%4=2) := by omega
      rw [oddDepth,dif_neg hk0]
  | succ r ih =>
      let z := 2^(2*r+1)*(4*q+3)
      have hpow : 2≤2^(2*r+1) := by
        rw [Nat.pow_succ]
        have hp: 0<2^(2*r) := Nat.pow_pos (by decide)
        omega
      have hq:3≤4*q+3 := by omega
      have hz6 : 6≤z := by
        dsimp [z]
        calc
          6 = 2*3 := by decide
          _ ≤ 2^(2*r+1)*3 := Nat.mul_le_mul_right 3 hpow
          _ ≤ 2^(2*r+1)*(4*q+3) := Nat.mul_le_mul_left _ hq
      have hz_even : z%2=0 := by
        have hz : z=2*(2^(2*r)*(4*q+3)) := by
          dsimp [z]
          rw [Nat.pow_succ]
          ac_rfl
        omega
      have hex : 2*(r+1)+1 = (2*r+1)+2 := by omega
      have htotal : 2^(2*(r+1)+1)*(4*q+3) = 4*z := by
        rw [hex,Nat.pow_add]
        simp only [show (2:Nat)^2=4 by decide]
        dsimp [z]
        ac_rfl
      rw [htotal]
      have h0 : 4≤4*z-2 ∧ (4*z-2)%4=2 := by omega
      have h1 : 4≤((4*z-2)-2)/2 ∧ (((4*z-2)-2)/2)%4=2 := by omega
      have h2 : ((((4*z-2)-2)/2)-2)/2 = z-2 := by omega
      rw [oddDepth,dif_pos h0,oddDepth,dif_pos h1,h2]
      change 1+(1+oddDepth (2^(2*r+1)*(4*q+3)-2))=2*(r+1)
      rw [ih]
      omega

/-- A full unbounded hierarchy of authentic Machine C blank-entry
    nonreachability exclusions, conditional on an explicit three-variable
    Diophantine equation. For each recursion depth parameter, it excludes
    infinitely many gate indices rather than relying on a fixed modulus. -/
theorem deep_low_gate_diophantine (r q u : Nat)
    (heq : 21*u-1=2^(2*r+1)*(4*q+3)) :
    ¬ BB6.Agent3.CReach 1 (32*u+4) := by
  have hRpos : 0 < 2^(2*r+1)*(4*q+3) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hu : 1≤u := by omega
  have hR : 2 ∣ 2^(2*r+1)*(4*q+3) := by
    refine ⟨2^(2*r)*(4*q+3),?_⟩
    rw [Nat.pow_succ]
    ac_rfl
  have hmod : (21*u-1)%2=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hR
  have huodd : u%2=1 := by omega
  have hK : 21*u-3 = 2^(2*r+1)*(4*q+3)-2 := by omega
  have hdepth : oddDepth (21*u-3)=2*r := by
    rw [hK]
    exact depth_pow_oddpart_three r q
  have hd : oddDepth (21*u-3)%2=0 := by rw [hdepth]; omega
  have hf : ∃qq:Nat,
      21*u-1=2^(oddDepth (21*u-3))*(8*qq+6) := by
    refine ⟨q,?_⟩
    rw [hdepth]
    calc
      21*u-1=2^(2*r+1)*(4*q+3) := heq
      _ = 2^(2*r)*(8*q+6) := by
        have he : 2*(4*q+3)=8*q+6 := by omega
        rw [Nat.pow_succ]
        calc
          (2^(2*r)*2)*(4*q+3) = 2^(2*r)*(2*(4*q+3)) := by ac_rfl
          _ = 2^(2*r)*(8*q+6) := by rw [he]
  exact low_gate_odd_u_2adic_unreachable u huodd hd hf

#print axioms depth_pow_oddpart_three
#print axioms deep_low_gate_diophantine
end BB6.Agent11
