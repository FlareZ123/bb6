import SecondRayZero
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray
open BB6.Agent46

private theorem four_pow_mul_four (t:Nat) (ht:1≤t) :
  4^t = 4*(4^(t-1)) := by
  calc
    4^t=4^((t-1)+1) := congrArg (fun z=>4^z) (by omega)
    _=4*(4^(t-1)) := by rw [Nat.pow_succ]; ac_rfl

/-- On the original high-fan sector, the odd-row bad-mod-4 criterion
    excludes the entire subfamily m+s=0 mod4 with s odd. -/
theorem fan_forbidden_parity (s t:Nat)
    (hmo : (FanArithmetic.m s t)%2=1)
    (hso:s%2=1) (hsum:(FanArithmetic.m s t+s)%4=0) :
    (FanArithmetic.q s t)%2=1 ∧
    (FanArithmetic.p s t+FanArithmetic.q s t)%4=2 ∧
    5<FanArithmetic.p s t := by
  let m:=FanArithmetic.m s t
  let a:=FanArithmetic.a s t
  let p:=FanArithmetic.p s t
  let q:=FanArithmetic.q s t
  let d:=FanArithmetic.d s t
  have ht:1≤t:=by dsimp [m,FanArithmetic.m] at hmo;omega
  have hB:3*m+4≤FanArithmetic.b s t := by
    dsimp [FanArithmetic.b,FanArithmetic.m,m]
    omega
  have hApow:4^t=4*4^(t-1) := four_pow_mul_four t ht
  have hA : 4≤a := by
    dsimp [a,FanArithmetic.a]
    have hbpos:1≤FanArithmetic.b s t:=by dsimp [FanArithmetic.b,FanArithmetic.m];omega
    have hpow : 4≤4^t := by
      rw [hApow]
      have hp := Nat.one_le_pow (t-1) 4 (by decide)
      omega
    have hh := Nat.le_mul_of_pos_right (4^t) hbpos
    omega
  have hAmod : a%4=0 := by
    dsimp [a,FanArithmetic.a]
    rw [hApow]
    have he : (4*4^(t-1))*FanArithmetic.b s t=
        4*(4^(t-1)*FanArithmetic.b s t) := by ac_rfl
    rw [he]
    omega
  have hP : p+3=4*a := by
    have hb := (FanArithmetic.bounds s t).2.2.2.2
    dsimp [p,FanArithmetic.p] at hb ⊢
    omega
  have hq : q+(2*a+3*m+7+3*s)=d := by
    have hb := (FanArithmetic.bounds s t).2.1
    dsimp [q,FanArithmetic.q]
    exact Nat.sub_add_cancel hb
  have hdmod : d%4=0 := by
    dsimp [d,FanArithmetic.d]
    have hpow:4^(m+1)=4*4^m := by rw [Nat.pow_succ];ac_rfl
    rw [hpow]
    have he:(4*4^m)*FanArithmetic.b s t=4*(4^m*FanArithmetic.b s t) := by ac_rfl
    rw [he]
    omega
  dsimp [m,p,q,a,d] at *
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Every such synthetic predecessor is genuinely absent from the blank
    Machine C section orbit, at ALL finite times. -/
theorem fan_blank_forbidden (s t time:Nat)
    (hmo:(FanArithmetic.m s t)%2=1)
    (hso:s%2=1) (hsum:(FanArithmetic.m s t+s)%4=0) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (FanArithmetic.source (FanArithmetic.m s t) ⟨s,by dsimp [FanArithmetic.m];omega⟩) := by
  intro h
  let m:=FanArithmetic.m s t
  have hm:m=s+t+1:=by dsimp [m,FanArithmetic.m]
  have ht:t=m-s-1:=by omega
  have hpair:FanArithmetic.source m ⟨s,by dsimp [m,FanArithmetic.m];omega⟩=
      (FanArithmetic.p s t,FanArithmetic.q s t) := by
    dsimp [FanArithmetic.source]
    rw [show m-s-1=t by omega]
  rw [hpair] at h
  obtain ⟨hkodd,hbad,hpbig⟩ := fan_forbidden_parity s t hmo hso hsum
  have hseed := BB6Agent38.blank_section_mod4 time
      (FanArithmetic.p s t) (FanArithmetic.q s t) h hkodd hbad
  have heq:FanArithmetic.p s t=5 := (Prod.mk.inj hseed).1
  omega

#print axioms fan_forbidden_parity
#print axioms fan_blank_forbidden
end BB6.Agent11Ray
