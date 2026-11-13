import QDepthHensel
import UParentBandEnvelope
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CascadeUParentBand887
open CascadeQDepthHensel CascadeRayDepthHensel CascadeUParentBandEnvelope CascadeResetInverse

theorem qNumerator_eq_affine (n j : Nat) :
  qNumerator n j = 28*(2:Int)^n-2*n+15-(2:Int)^(j+4)*(2*n+3) := by
  dsimp [qNumerator,CascadeRayPeriod.signedZ]
  have hn : (2:Int)^(n+2)=4*(2:Int)^n := by
    rw [Int.pow_add]
    rw [show (2:Int)^2=4 by decide]
    omega
  have hj : (2:Int)^(j+4)=8*(2:Int)^(j+1) := by
    rw [show j+4=(j+1)+3 by omega,Int.pow_add]
    rw [show (2:Int)^3=8 by decide]
    rw [Int.mul_comm ((2:Int)^(j+1)) (8:Int)]
  rw [hn,hj]
  simp only [Int.mul_sub,Int.mul_add]
  simp only [←Int.mul_assoc]
  omega

theorem qNumerator_eq_U (j p U : Nat) (hp:p=2^885)
    (hform : U+2*887+2^(j+4)*1777=112*p+15) :
    qNumerator 887 j = (U:Int) := by
  rw [qNumerator_eq_affine]
  have hpI : (p:Int)=(2:Int)^885 := by exact_mod_cast hp
  have hpow : (2:Int)^887=4*(2:Int)^885 := by
    rw [show 887=885+2 by omega,Int.pow_add]
    rw [show (2:Int)^2=4 by decide]
    omega
  have hformI : (U:Int)+2*887+(2:Int)^(j+4)*1777=112*(p:Int)+15 := by
    exact_mod_cast hform
  rw [hpI] at hformI
  have hpow' : 112*(2:Int)^885=28*(2:Int)^887 := by
    rw [hpow]
    omega
  rw [hpow'] at hformI
  omega

/-- The exact t=1 child coordinate determined by the affine U equation. -/
def z0_887 (j:Nat) : Nat := (56*2^885-902-2^(j+3)*1777)/9

theorem z0_eq_of_U (j p U z:Nat) (hp:p=2^885)
    (hform:U+2*887+2^(j+4)*1777=112*p+15)
    (hU:U=9*(2*z+5)) : z=z0_887 j := by
  have hterm : 2^(j+4)*1777=2*(2^(j+3)*1777) := by
    rw [Nat.pow_succ]
    ac_rfl
  have hlin : 18*z+2*(2^(j+3)*1777)=112*p-1804 := by
    rw [hU,hterm] at hform
    omega
  have hnum : 9*z+2^(j+3)*1777=56*p-902 := by omega
  have hnum' : 9*z+2^(j+3)*1777=56*2^885-902 := by
    rw [hp] at hnum
    exact hnum
  have hdiv : (56*2^885-902-2^(j+3)*1777)/9=z := by omega
  simpa [z0_887] using hdiv.symm


end CascadeUParentBand887
