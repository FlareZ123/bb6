import RawCylinder

namespace SheepEvenPhasePump
open SheepRawCylinder

/-- Exact relation of two generic even-section returns when their first
    raw successors differ by a multiplicative power-of-two shift about 1. -/
theorem successor_shift {a d x x' y y' : Nat}
    (g : Generic a x y) (g' : Generic a x' y')
    (h : (2^(a+1)+1)*x' + 2^(a+1)*a + 2^d*(3*2^a) =
        2^d*((2^(a+1)+1)*x + 2^(a+1)*a) + 3*2^a) :
    y' + 2^d = 2^d*y + 1 := by
  have h1 := one_affine g
  have h2 := one_affine g'
  have h0 : 2^(a+1)*y' + 2^a + 2^d*(3*2^a) =
      2^d*(2^(a+1)*y+2^a)+3*2^a := by
    rwa [h1,h2]
  let q := 2^a
  let b := 2^d
  have h0' : 2*(q*y')+q+3*(b*q)=2*(q*(b*y))+b*q+3*q := by
    have hq : 2^(a+1) = 2*q := by simp [q,Nat.pow_succ,Nat.mul_comm]
    rw [hq] at h0
    change (2*q)*y'+q+b*(3*q)=b*((2*q)*y+q)+3*q at h0
    calc
      _ = (2*q)*y'+q+b*(3*q) := by ac_rfl
      _ = b*((2*q)*y+q)+3*q := h0
      _ = _ := by rw [Nat.mul_add]; ac_rfl
  have hh : q*y'+b*q=q*(b*y)+q := by omega
  have hc : q*(y'+b)=q*(b*y+1) := by
    rw [Nat.mul_add,Nat.mul_add,Nat.mul_one,Nat.mul_comm q b]
    exact hh
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hc

/-- The exact genuine accelerated outputs lie on the same multiplicative
    orbit about 1; every intermediate raw step is certified. -/
theorem odd_phase_pump {a d x x' y y' h v : Nat}
    (g : Generic a x y) (g' : Generic a x' y')
    (hy : y = 1+2^h*v) (hv : v%2=1)
    (hl : 5≤y) (hl' : 5≤y')
    (ha : (2^(a+1)+1)*x' + 2^(a+1)*a + 2^d*(3*2^a) =
        2^d*((2^(a+1)+1)*x + 2^(a+1)*a) + 3*2^a) :
    SheepEven.Steps (h+1) x (1+3^h*v) ∧
    SheepEven.Steps (h+d+1) x' (1+3^d*(3^h*v)) ∧
    (1+3^h*v)%2=0 ∧ (1+3^d*(3^h*v))%2=0 := by
  have hs := successor_shift g g' ha
  have hy' : y' = 1+2^(h+d)*v := by
    rw [hy, Nat.mul_add, Nat.mul_one] at hs
    rw [Nat.pow_add]
    have hh : 2^h*2^d*v=2^d*(2^h*v) := by ac_rfl
    rw [hh]
    omega
  have hfirst := SheepEven.odd_block h v (Or.inr (hy ▸ hl))
  have hnext := SheepEven.odd_block (h+d) v (Or.inr (hy' ▸ hl'))
  have hpow : 3^(h+d)*v=3^d*(3^h*v) := by rw [Nat.pow_add]; ac_rfl
  have hodd (k : Nat) : (1+3^k*v)%2=0 := by
    rw [Nat.add_mod,Nat.mul_mod,Nat.pow_mod]
    simp [hv]
  refine ⟨SheepEven.Steps.cons (generic_source g) (hy.symm ▸ hfirst), ?_,hodd h,?_⟩
  · rw [← hpow]
    exact SheepEven.Steps.cons (generic_source g') (hy'.symm ▸ hnext)
  · rw [← hpow]; exact hodd (h+d)

#print axioms successor_shift
#print axioms odd_phase_pump
end SheepEvenPhasePump
