import Std
import Lean.Elab.Tactic.Omega

namespace CapMacro

/-- The largest r for which 3^r*q <= b (on 0 < q <= b).
    Divide the bound, rather than multiplying the coordinate. -/
def tripleCount (b q : Nat) : Nat :=
  if q = 0 ∨ b < 3*q then 0 else tripleCount (b/3) q + 1
termination_by b
decreasing_by omega

theorem tripleCount_spec {b q : Nat} (hq : 0<q) (hb : q≤b) :
    3^(tripleCount b q)*q≤b ∧ b<3^(tripleCount b q+1)*q := by
  rw [tripleCount]
  split
  next h => simp; omega
  next h =>
    have hq' : q≤b/3 := by omega
    obtain ⟨hlo,hhi⟩ := tripleCount_spec hq hq'
    let v := 3^(tripleCount (b/3) q)*q
    have h1 : 3^(tripleCount (b/3) q+1)*q=3*v := by
      rw [Nat.pow_succ]; dsimp [v]; ac_rfl
    have h2 : 3^(tripleCount (b/3) q+1+1)*q=9*v := by
      rw [Nat.pow_succ,Nat.pow_succ]; dsimp [v]
      calc
        3^(tripleCount (b/3) q)*3*3*q = (3*3)*(3^(tripleCount (b/3) q)*q) := by ac_rfl
        _ = _ := by rfl
    change v≤b/3 at hlo
    rw [h1] at hhi
    rw [h1,h2]
    omega
termination_by b
decreasing_by omega

/-- Any two exponents whose products straddle the same threshold agree. -/
theorem triple_window_unique {b q r s : Nat} (_hq : 0<q)
    (hr : 3^r*q≤b ∧ b<3^(r+1)*q)
    (hs : 3^s*q≤b ∧ b<3^(s+1)*q) : r=s := by
  by_cases h : r=s
  · exact h
  · rcases Nat.lt_or_gt_of_ne h with hlt|hgt
    · have hp : 3^(r+1)≤3^s := Nat.pow_le_pow_right (by decide) (by omega)
      have hm := Nat.mul_le_mul_right q hp
      omega
    · have hp : 3^(s+1)≤3^r := Nat.pow_le_pow_right (by decide) (by omega)
      have hm := Nat.mul_le_mul_right q hp
      omega

/-- Positive-coordinate band exit. Its power-of-three product is in
    a width-<3 interval, and the parity is preserved. -/
theorem positive_window {p q : Nat} (hq : 0<q) (hb : q≤2*p-2) :
    let r := tripleCount (2*p-2) q
    let z := 3^r*q
    let u := 3*z
    q≤z ∧ z≤2*p-2 ∧ 2*p-1≤u ∧ u≤6*p-6 ∧ z%2=q%2 := by
  dsimp
  obtain ⟨hlo,hhi⟩ := tripleCount_spec hq hb
  have hp : 0<3^(tripleCount (2*p-2) q) := Nat.pow_pos (by decide)
  have hqlo := Nat.le_mul_of_pos_left q hp
  rw [Nat.pow_succ] at hhi
  have h3 : (3^(tripleCount (2*p-2) q)*3)*q=3*(3^(tripleCount (2*p-2) q)*q) := by ac_rfl
  rw [h3] at hhi
  have hpar : ∀ n : Nat, 3^n%2=1 := by
    intro n
    induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ,Nat.mul_mod,ih]
  refine ⟨hqlo,hlo,by omega,by omega,?_⟩
  rw [Nat.mul_mod,hpar]
  simp

#print axioms tripleCount_spec
#print axioms triple_window_unique
#print axioms positive_window
end CapMacro
