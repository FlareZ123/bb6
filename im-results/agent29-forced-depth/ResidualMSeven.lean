import ResidualExponential
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 5000000
namespace BB6.Agent29Barrier

private theorem mseven_v_bound (v d:Nat)
    (hv:v%4=2) (hdiv:21845 ∣ v*2^d+7) : 15018≤v := by
  have hred := reduce_period 21845 v 7 d 8 (by decide) (by decide) hdiv
  have ht : d%16=0 ∨ d%16=1 ∨ d%16=2 ∨ d%16=3 ∨
    d%16=4 ∨ d%16=5 ∨ d%16=6 ∨ d%16=7 ∨
    d%16=8 ∨ d%16=9 ∨ d%16=10 ∨ d%16=11 ∨
    d%16=12 ∨ d%16=13 ∨ d%16=14 ∨ d%16=15 := by omega
  rcases ht with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    rw [h] at hred <;>
    simp at hred <;>
    omega

/-- For m=7 the exact finite modular minimum, assuming Y=4 mod 12. -/
theorem mseven_residual_ge_45052 (j k d Y : Nat)
    (hstop : k+j+26=2^16*(j+3))
    (hscale:2^d*(Y+2)=k+2) (hmod:Y%12=4) : 45052≤Y := by
  let v:=(Y+2)/3
  have hv: Y+2=3*v := by dsimp [v]; omega
  have hv4:v%4=2 := by dsimp [v]; omega
  have hpow : 2^16=65536 := by decide
  rw [hpow] at hstop
  have hEq: v*2^d+7=21845*(j+3) := by
    have hScale:2^d*(Y+2)=3*(v*2^d) := by rw [hv]; ac_rfl
    rw [hScale] at hscale
    omega
  have hdiv: 21845 ∣ v*2^d+7 := ⟨j+3,by simpa [Nat.mul_comm] using hEq⟩
  have hmin := mseven_v_bound v d hv4 hdiv
  omega

#print axioms mseven_v_bound
#print axioms mseven_residual_ge_45052
end BB6.Agent29Barrier
