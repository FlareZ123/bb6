import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Barrier

theorem shrink (q v m d L : Nat)
    (hperiod : 2^(2*L) = 3*q+1)
    (hlarge : 2*L ≤ d) (hdiv : q ∣ v*2^d + m) :
    q ∣ v*2^(d-2*L)+m := by
  let e := d-2*L
  have hd : d = 2*L+e := by dsimp [e]; omega
  have hp : 2^d = (3*q+1)*2^e := by
    rw [hd,Nat.pow_add,hperiod]
  have heq : v*2^d+m = q*(3*v*2^e)+(v*2^e+m) := by
    rw [hp]
    simp only [Nat.add_mul, Nat.mul_add]
    ac_rfl
  have hmul : q ∣ q*(3*v*2^e) := Nat.dvd_mul_right q _
  rw [heq] at hdiv
  exact (Nat.dvd_add_iff_right hmul).mpr hdiv

theorem reduce_period (q v m d L : Nat) (hL : 0<L)
    (hperiod : 2^(2*L) = 3*q+1)
    (hdiv : q ∣ v*2^d+m) : q ∣ v*2^(d%(2*L))+m := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hd : d<2*L
    · simpa [Nat.mod_eq_of_lt hd] using hdiv
    · have hlarge : 2*L≤d := by omega
      have hlt : d-2*L<d := by omega
      have hrec := ih (d-2*L) hlt (shrink q v m d L hperiod hlarge hdiv)
      simpa only [Nat.mod_eq_sub_mod hlarge] using hrec

#print axioms shrink
#print axioms reduce_period
end BB6.Agent29Barrier
