import Lean
import Lean.Elab.Tactic.Omega

namespace NeedleRotation.FourResidue

theorem N_mod70_aux (k : Nat) : 9^(3*k+1)%70=9 ∨ 9^(3*k+1)%70=51 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 3*(k+1)+1=3*k+1+3 by omega,Nat.pow_add,Nat.mul_mod]
    rcases ih with h|h <;> rw [h] <;> decide

theorem N_mod70 (r : Nat) (hr : r%3=1) : 9^r%70=9 ∨ 9^r%70=51 := by
  rw [show r=3*(r/3)+1 by omega]
  exact N_mod70_aux _

/-- The v=4 predecessor of a cancellation feeder has no N-divisible
    correction in the low side, for every r = 1 modulo 3. -/
theorem four_no_N_dvd (r a m : Nat) (hr : 8≤r) (hres : r%3=1)
    (ha : 2*a=9^r+5) (hm : 0<m) (hma : m≤a) :
    ¬ (9^r:Int)∣15-70*(m:Int) := by
  intro hd
  obtain ⟨t,ht⟩ := hd
  let N : Nat := 9^r
  have hN : 729≤N := Nat.pow_le_pow_right (by decide : 0<(9:Nat)) (show 3≤r by omega)
  have hNp : 0<(N:Int) := by omega
  let k := -t
  have hk : 70*(m:Int)-15=(N:Int)*k := by
    dsimp [k,N]
    have hcast : (9^r:Int)=((9^r:Nat):Int) := by simp
    rw [hcast] at ht
    grind
  have hk0 : 0≤k := by
    by_cases h : 0≤k
    · exact h
    have hh := Int.mul_le_mul_of_nonneg_left (show k≤0 by omega) (Int.le_of_lt hNp)
    simp only [Int.mul_zero] at hh
    omega
  have hk35 : k≤35 := by
    by_cases h : k≤35
    · exact h
    have hh := Int.mul_le_mul_of_nonneg_left (show 36≤k by omega) (Int.le_of_lt hNp)
    rw [Int.mul_comm (N:Int) 36] at hh
    change 2*a=N+5 at ha
    omega
  have hmod := congrArg (fun x : Int => x%70) hk
  change (70*(m:Int)-15)%70=((N:Int)*k)%70 at hmod
  rw [Int.mul_emod] at hmod
  have hNmod := N_mod70 r hres
  rcases hNmod with h|h
  · have hcast : (N:Int)%70=9 := by exact_mod_cast h
    rw [hcast,Int.emod_eq_of_lt hk0 (by omega)] at hmod
    omega
  · have hcast : (N:Int)%70=51 := by exact_mod_cast h
    rw [hcast,Int.emod_eq_of_lt hk0 (by omega)] at hmod
    omega

#print axioms four_no_N_dvd
end NeedleRotation.FourResidue
