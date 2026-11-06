import ResidualExponential
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Barrier

private theorem mthree_v_bound (v d : Nat)
    (hv:v%4=2) (hdiv:85 ∣ v*2^d+3) : 74≤v := by
  have hred := reduce_period 85 v 3 d 4 (by decide) (by decide) hdiv
  have ht : d%8=0 ∨ d%8=1 ∨ d%8=2 ∨ d%8=3 ∨
    d%8=4 ∨ d%8=5 ∨ d%8=6 ∨ d%8=7 := by omega
  rcases ht with h|h|h|h|h|h|h|h <;>
    rw [h] at hred <;>
    simp at hred <;>
    omega

private theorem mfive_v_bound (v d : Nat)
    (hv:v%4=2) (hdiv:1365 ∣ v*2^d+5) : 170≤v := by
  have hred := reduce_period 1365 v 5 d 6 (by decide) (by decide) hdiv
  have ht : d%12=0 ∨ d%12=1 ∨ d%12=2 ∨ d%12=3 ∨
    d%12=4 ∨ d%12=5 ∨ d%12=6 ∨ d%12=7 ∨
    d%12=8 ∨ d%12=9 ∨ d%12=10 ∨ d%12=11 := by omega
  rcases ht with h|h|h|h|h|h|h|h|h|h|h|h <;>
    rw [h] at hred <;>
    simp at hred <;>
    omega

/-- For m=3 the exact finite modular minimum, assuming Y=4 mod 12. -/
theorem mthree_residual_ge_220 (j k d Y : Nat)
    (hstop : k+j+14=2^8*(j+3))
    (hscale:2^d*(Y+2)=k+2) (hmod:Y%12=4) : 220≤Y := by
  let v:=(Y+2)/3
  have hv: Y+2=3*v := by dsimp [v]; omega
  have hv4:v%4=2 := by dsimp [v]; omega
  have hpow : 2^8=256 := by decide
  rw [hpow] at hstop
  have hEq: v*2^d+3=85*(j+3) := by
    have hScale:2^d*(Y+2)=3*(v*2^d) := by rw [hv]; ac_rfl
    rw [hScale] at hscale
    omega
  have hdiv: 85 ∣ v*2^d+3 := ⟨j+3,by simpa [Nat.mul_comm] using hEq⟩
  have hmin := mthree_v_bound v d hv4 hdiv
  omega

/-- For m=5 the exact finite modular minimum, assuming Y=4 mod 12. -/
theorem mfive_residual_ge_508 (j k d Y : Nat)
    (hstop : k+j+20=2^12*(j+3))
    (hscale:2^d*(Y+2)=k+2) (hmod:Y%12=4) : 508≤Y := by
  let v:=(Y+2)/3
  have hv: Y+2=3*v := by dsimp [v]; omega
  have hv4:v%4=2 := by dsimp [v]; omega
  have hpow : 2^12=4096 := by decide
  rw [hpow] at hstop
  have hEq: v*2^d+5=1365*(j+3) := by
    have hScale:2^d*(Y+2)=3*(v*2^d) := by rw [hv]; ac_rfl
    rw [hScale] at hscale
    omega
  have hdiv: 1365 ∣ v*2^d+5 := ⟨j+3,by simpa [Nat.mul_comm] using hEq⟩
  have hmin := mfive_v_bound v d hv4 hdiv
  omega

/-- From depth seven onward, the source-exact exponential bound is above 220. -/
theorem power_seven_linear (m:Nat) (hm:7≤m) :
    6*m+221≤2^(m+2) := by
  have hall : ∀ n:Nat, 6*(n+7)+221≤2^(n+9) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        have hpow:2^((n+1)+9)=2*2^(n+9) := by
          have he:(n+1)+9=(n+9)+1 := by omega
          rw [he,Nat.pow_succ]
          omega
        rw [hpow]
        omega
  have h:=hall (m-7)
  have he1:m-7+7=m := by omega
  have he2:m-7+9=m+2 := by omega
  rw [he1,he2] at h
  exact h

/-- A UNIFORM lower bound for all odd m>=3 second-stopping residuals
    in the original source's 4-mod-12 affine residual sector. -/
theorem odd_residual_ge_220 (j m k d Y : Nat)
    (hm:3≤m) (hodd:m%2=1)
    (hstop:k+j+3*m+5=2^(2*m+2)*(j+3))
    (hscale:2^d*(Y+2)=k+2) (hmod:Y%12=4) : 220≤Y := by
  have hc:m=3 ∨ m=5 ∨ 7≤m := by omega
  rcases hc with h3 | h5 | hlarge
  · subst m
    exact mthree_residual_ge_220 j k d Y (by simpa using hstop) hscale hmod
  · subst m
    have hmin := mfive_residual_ge_508 j k d Y (by simpa using hstop) hscale hmod
    omega
  · have hb := second_stop_odd_residual_exponential j m k d Y
      (by omega) hodd hstop hscale
    have hp := power_seven_linear m hlarge
    omega

#print axioms mthree_v_bound
#print axioms mfive_v_bound
#print axioms mthree_residual_ge_220
#print axioms mfive_residual_ge_508
#print axioms power_seven_linear
#print axioms odd_residual_ge_220
end BB6.Agent29Barrier
