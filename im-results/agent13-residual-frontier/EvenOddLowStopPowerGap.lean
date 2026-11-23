import EvenOddAllValuationParent
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowFanPower
open BB6.Agent46

private theorem linear_le_power (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- A structural gap in the ENTIRE genuine necessary low-stop ray
    m=512z+67.  The source four-step predecessor target has
    u+6z+1=2^(1024z+129). Its odd-bounce mass Q=346u+54 is
    strictly between the consecutive powers 2^(1024z+137) and
    2^(1024z+138), for every unbounded z. No finite search is involved. -/
theorem low_mass_strict_gap
    (z u : Nat)
    (hu : u+6*z+1=2^(1024*z+129)) :
    2^(1024*z+137) < 346*u+54 ∧
      346*u+54 < 2^(1024*z+138) := by
  let t := 1024*z+129
  have hlin : t+1 ≤ 2^t := linear_le_power t
  have heq : 346*u+54+2076*z+292=346*2^t := by
    dsimp [t] at *
    omega
  have hlo : 256*2^t < 346*u+54 := by
    have ht : t=1024*z+129 := rfl
    omega
  have hhi : 346*u+54 < 512*2^t := by omega
  have hboundlo : 2^(t+8) < 346*u+54 := by
    rw [Nat.pow_add]
    simp only [show (2:Nat)^8=256 by decide] at *
    omega
  have hboundhi : 346*u+54 < 2^(t+9) := by
    rw [Nat.pow_add]
    simp only [show (2:Nat)^9=512 by decide] at *
    omega
  dsimp [t] at hboundlo hboundhi
  constructor <;> convert (by assumption : _) using 1 <;> congr 1 <;> omega

/-- The necessary low-stop source mass is never dyadically pure. This
    removes the previously unresolved exceptional a=1 predecessor branch
    for ALL z, including those with arbitrarily large 2-adic valuation. -/
theorem low_mass_not_power_two
    (z u : Nat)
    (hu : u+6*z+1=2^(1024*z+129)) :
    ∀ n : Nat, 346*u+54 ≠ 2^n := by
  obtain ⟨hlo,hhi⟩ := low_mass_strict_gap z u hu
  intro n hn
  by_cases hle : n ≤ 1024*z+137
  · have hmon : 2^n ≤ 2^(1024*z+137) :=
      Nat.pow_le_pow_right (by omega) hle
    omega
  · have hbig : 1024*z+138 ≤ n := by omega
    have hmon : 2^(1024*z+138) ≤ 2^n :=
      Nat.pow_le_pow_right (by omega) hbig
    omega

/-- Source-complete ordinary-parent classification for EVERY necessary
    Machine C low-stop target on m=512z+67: all original incoming
    source edges are odd high-bounce edges at EVEN, UNBOUNDED depth.
    This is not a blank-reachability decision; surviving parents remain. -/
theorem all_low_ray_parents_are_even_bounce
    (z u a k : Nat)
    (hu : u+6*z+1=2^(1024*z+129))
    (hedge : secNext (a,k)=some (180*u+28,166*u+25)) :
    ∃ n : Nat, n%2=0 ∧ 3≤a ∧ a<2*k ∧
      346*u+54=2^n*(2*(a-1)+8) ∧
      (2*k-a+3)+(2*(a-1)+8)+3*n=512*u+78 := by
  have hlin : (1024*z+129)+1 ≤ 2^(1024*z+129) :=
    linear_le_power _
  have hu64 : 64≤u := by omega
  have hbig : 64 ≤ (180*u+28)+(166*u+25)+1 := by omega
  have hnp : ∀ n : Nat,
      (180*u+28)+(166*u+25)+1≠2^n := by
    intro n hn
    exact (low_mass_not_power_two z u hu n) (by omega)
  obtain ⟨n,hn,ha,hlow,hpow,hcost⟩ :=
    BB6.Agent13AllFan.even_odd_nonpower_parent
      a k (180*u+28) (166*u+25)
      (by omega) (by omega) (by omega)
      hbig hnp hedge
  refine ⟨n,hn,ha,hlow,?_,?_⟩ <;> omega

#print axioms low_mass_strict_gap
#print axioms low_mass_not_power_two
#print axioms all_low_ray_parents_are_even_bounce
end BB6.Agent13LowFanPower
