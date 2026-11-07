import SheepSharper
import ResidueGap

namespace SheepSharper

private theorem pow_three_odd (h : Nat) : (3^h)%2=1 := by
  induction h with
  | zero => decide
  | succ h ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

private theorem K_odd (h a : Nat) (ha : 2 ≤ a) : K h a%2=1 := by
  have hc : (2*a-3)%2=1 := by omega
  have hp : (2^(h+1))%2=0 := by
    rw [Nat.pow_succ, Nat.mul_mod]
    simp
  simp [K, Nat.add_mod, Nat.mul_mod, hc, hp, pow_three_odd]

/-- For h>=15, the exact generic parent Diophantine equation has no
    solution when the source valuation exceeds our 5/3-slope threshold. -/
theorem no_power_generic_three (j h a v : Nat)
    (hh : 15 ≤ h) (ha : cutoff h ≤ a) :
    2^(j+h+1) ≠ 3^h*(2^(a+1)+1)*v + K h a := by
  intro heq
  have gap := val_gap h a hh ha
  have hodd : K h a%2=1 := K_odd h a (by
    have hcutoff:30≤cutoff h := by unfold cutoff; omega
    omega)
  have hpowmax : 2^a < 2^(a+1)+1 := by
    have hp : 2^a < 2^(a+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hlt : K h a < 2^(a+1)+1 := Nat.lt_trans gap.2 hpowmax
  have hm : 2^(j+h+1) % (2^(a+1)+1) = K h a := by
    rw [heq]
    have hz : (3^h*(2^(a+1)+1)*v) % (2^(a+1)+1) = 0 := by
      simp [Nat.mul_mod]
    rw [Nat.add_mod,hz, Nat.mod_eq_of_lt hlt]
    simp [Nat.mod_eq_of_lt hlt]
  exact (SheepResidueGap.gap a (j+h+1) (K h a) hodd gap.1 gap.2) hm

/-- The 8/5-slope sharper obstruction for h>=100. -/
theorem no_power_generic_five (j h a v : Nat)
    (hh : 100 ≤ h) (ha : cutoffFive h ≤ a) :
    2^(j+h+1) ≠ 3^h*(2^(a+1)+1)*v + K h a := by
  intro heq
  have gap := val_gap_five h a hh ha
  have hodd : K h a%2=1 := K_odd h a (by
    have hcutoff:168≤cutoffFive h := by unfold cutoffFive; omega
    omega)
  have hpowmax : 2^a < 2^(a+1)+1 := by
    have hp : 2^a < 2^(a+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hlt : K h a < 2^(a+1)+1 := Nat.lt_trans gap.2 hpowmax
  have hm : 2^(j+h+1) % (2^(a+1)+1) = K h a := by
    rw [heq]
    have hz : (3^h*(2^(a+1)+1)*v) % (2^(a+1)+1) = 0 := by
      simp [Nat.mul_mod]
    rw [Nat.add_mod,hz, Nat.mod_eq_of_lt hlt]
    simp [Nat.mod_eq_of_lt hlt]
  exact (SheepResidueGap.gap a (j+h+1) (K h a) hodd gap.1 gap.2) hm

/-- Bridges a positive-valued generic source equation to the signed gap. -/
theorem generic_source_diophantine (a h v j : Nat) (ha : 3 ≤ a)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
         =2^(j+h+1)+3*3^h) :
    2^(j+h+1) = 3^h*(2^(a+1)+1)*v + K h a := by
  have haa : 2*a=(2*a-3)+3 := by omega
  have hm : 2*a*3^h=3^h*(2*a-3)+3*3^h := by
    calc
      2*a*3^h = ((2*a-3)+3)*3^h := by rw [←haa]
      _ = (2*a-3)*3^h+3*3^h := by rw [Nat.add_mul]
      _ = 3^h*(2*a-3)+3*3^h := by rw [Nat.mul_comm (2*a-3) (3^h)]
  unfold K
  omega

#print axioms generic_source_diophantine

#print axioms no_power_generic_three
#print axioms no_power_generic_five
end SheepSharper
