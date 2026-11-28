import DyadicHighValid
import DyadicValuation

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone

private theorem I_dvd (m n : Nat) (h : m≤n) : I m∣I n := by
  refine ⟨I (n-m),?_⟩
  rw [I_split h]
  ac_rfl

/-- An exact valuation witness of v implies divisibility by every
    smaller dyadic power, even for negative signed cone representatives. -/
theorem valvalid_divisor (b v n : Nat) (s : Pair)
    (hv : ValValid b s v) (hn : n+2≤v) :
    I (n+2)∣q s := by
  have he : q s = I v+I (v+1)*(q s/I (v+1)) := by
    have hsplit := Int.emod_add_mul_ediv (q s) (I (v+1))
    rw [hv.2] at hsplit
    omega
  have h1 : I (n+2)∣I v := I_dvd _ _ hn
  have h2 : I (n+2)∣I (v+1) := I_dvd _ _ (by omega)
  have h3 : I (n+2)∣I (v+1)*(q s/I (v+1)) :=
    Int.dvd_trans h2 (Int.dvd_mul_right _ _)
  rw [he]
  exact Int.dvd_add h1 h3

/-- The seemingly extra HighValid test of the modular cone is
    mathematically implied by its preceding guards ValValid and
    Allowed: the signed high parent is necessarily integral. -/
theorem allowed_high_valid (b v n : Nat) (s : Pair)
    (hv : ValValid b s v) (ha : Allowed s v n) :
    HighValid s n := by
  have hq : I (n+2)∣q s := valvalid_divisor b v n s hv ha.1
  exact high_valid_of_valuation s n hq ha.2

#print axioms allowed_high_valid
end BB6.Agent21Duality
