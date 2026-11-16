import U5Y3ParentFan
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000

namespace BB6.Agent3U5M16Residual
open BB6.Agent3U5DepthFan

/-- The U5 residual equations force t=19 (mod 32) on the w=21 (mod32)
    cylinder. This is the only congruence needed by the M16 parent filter. -/
theorem u5_m8_t_mod32 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%32=21) : t%32=19 := by
  have hid : 211*(m+1)+10669+22155*(8*w)=160*2^(201+3360*w) := by omega
  have hdiv : 256∣2^(201+3360*w) := by
    change 2^8∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod : (2^(201+3360*w))%256=0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  have hidForT : 211*(8*t+1)+10669+22155*(8*w)=160*2^(201+3360*w) := by
    simpa [hp] using hid
  have hmod : (211*(8*t+1)+10669+22155*(8*w))%256=0 := by
    rw [hidForT,Nat.mul_mod,hpowmod]
  have hlin : 211*(8*t+1)+10669+22155*(8*w)=8*(211*t+1360+22155*w) := by omega
  rw [hlin] at hmod
  have hBmod : (211*t+1360+22155*w)%32=0 := by omega
  omega

/-- On the additional w=37 (mod128) cylinder, the U5 residual
    equations force the stronger t=99 (mod128) class. -/
theorem u5_m8_t_mod128_w37 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%128=37) : t%128=99 := by
  have hid : 211*(m+1)+10669+22155*(8*w)=160*2^(201+3360*w) := by omega
  have hdiv : 1024∣2^(201+3360*w) := by
    change 2^10∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod : (2^(201+3360*w))%1024=0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  have hidForT :
      211*(8*t+1)+10669+22155*(8*w)=160*2^(201+3360*w) := by
    simpa [hp] using hid
  have hmod :
      (211*(8*t+1)+10669+22155*(8*w))%1024=0 := by
    rw [hidForT,Nat.mul_mod,hpowmod]
  have hlin :
      211*(8*t+1)+10669+22155*(8*w)=
        8*(211*t+1360+22155*w) := by omega
  rw [hlin] at hmod
  have hBmod : (211*t+1360+22155*w)%128=0 := by omega
  omega

end BB6.Agent3U5M16Residual
