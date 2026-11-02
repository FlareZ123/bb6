import Lean
import BExit

namespace BB6.CryptidBRun

/-- A B run ending outside the B residue has consumed the full
three-adic valuation of its affine invariant. -/
theorem terminal_no_extra_three {j n z : Nat}
    (h : BRun j n z) (hz : z%3 ≠ 2) :
    ¬ 3^(j+1) ∣ 5*n+11 := by
  intro hd
  obtain ⟨q,hq⟩ := hd
  have heq : 3^j*(5*z+11)=3^j*(3*(8^j*q)) := by
    calc
      3^j*(5*z+11) = 8^j*(5*n+11) := run_scale h
      _ = 8^j*(3^(j+1)*q) := by rw [hq]
      _ = 3^j*(3*(8^j*q)) := by rw [Nat.pow_succ]; ac_rfl
  have hp : 0 < 3^j := Nat.pow_pos (by decide)
  have hf : 5*z+11=3*(8^j*q) := Nat.eq_of_mul_eq_mul_left hp heq
  omega

/-- The exact maximum number of successive B updates from n is
characterized by adjacent powers of three. -/
theorem exact_B_exit (n : Nat) :
    ∃ j z, BRun j n z ∧ z%3≠2 ∧
      3^j ∣ 5*n+11 ∧ ¬3^(j+1) ∣ 5*n+11 := by
  obtain ⟨j,z,h,hz⟩ := eventually_non_B n
  exact ⟨j,z,h,hz,run_requires_three_power h,terminal_no_extra_three h hz⟩

#print axioms terminal_no_extra_three
#print axioms exact_B_exit
end BB6.CryptidBRun
