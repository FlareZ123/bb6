import NeedleCancelMod35
import Lean.Elab.Tactic.Omega

namespace CancellationEleven
open NeedleCancelMod35

def idx (t:Nat) := 4152608179 + 35697042810*t

private theorem cycle4099 (a period n : Nat) (hc:(a^period)%4099=1) :
    a^n%4099=a^(n%period)%4099 := by
  have hr : period*(n/period)+n%period=n := by
    have hh := Nat.mod_add_div n period
    omega
  have hp : (a^(period*(n/period)))%4099=1 := by
    rw [Nat.pow_mul,Nat.pow_mod,hc]
    simp
  calc
    (a^n)%4099 = (a^(period*(n/period)+n%period))%4099 := by rw [hr]
    _ = (a^(n%period))%4099 := by
      rw [Nat.pow_add,Nat.mul_mod,hp]
      omega

private theorem nine_period31 (n : Nat) :
    9^(31*n+17)%8196=4125 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [show 31*(n+1)+17=(31*n+17)+31 by omega,
        Nat.pow_add,Nat.mul_mod,ih,
        show (9:Nat)^31%8196=2733 by decide]

private theorem v_mod4098 (t:Nat) : v (idx t)%4098=2064 := by
  have hr : idx t=31*(133955102+1151517510*t)+17 := by
    dsimp [idx]
    omega
  have h := nine_period31 (133955102+1151517510*t)
  rw [←hr] at h
  dsimp [v]
  omega

private theorem two_mod4099 (t:Nat) :
    2^(v (idx t))%4099=24 := by
  have h:=cycle4099 2 4098 (v (idx t))
    (by rw [←Nat.powMod_def]; decide : (2:Nat)^4098%4099=1)
  rw [v_mod4098] at h
  have hsmall : (2:Nat)^2064%4099=24 := by
    rw [←Nat.powMod_def]
    decide
  exact h.trans hsmall

private theorem xb_mod4099 (t:Nat) : xb (idx t)%4099=48 := by
  unfold xb
  rw [Nat.pow_succ,Nat.mul_mod,two_mod4099]

private theorem r_mod2049 (t:Nat) : idx t%2049=280 := by
  dsimp [idx]
  omega

private theorem A2pow_mod4099 (t:Nat) :
    ((xb (idx t))^2)^(idx t)%4099=2719 := by
  have hx : xb (idx t)%4099=48 := xb_mod4099 t
  have hsq : ((xb (idx t))^2)%4099=2304 := by
    rw [Nat.pow_mod,hx]
  have hpow : (((xb (idx t))^2)^(idx t))%4099 = (2304^(idx t))%4099 := by
    rw [Nat.pow_mod,hsq]
  rw [hpow,cycle4099 2304 2049 (idx t)
    (by rw [←Nat.powMod_def]; decide : (2304:Nat)^2049%4099=1),r_mod2049]
  rw [←Nat.powMod_def]
  decide

private theorem ninepow_mod4099 (t:Nat) :
    9^(idx t)%4099=2955 := by
  rw [cycle4099 9 2049 (idx t) (by rw [←Nat.powMod_def]; decide : (9:Nat)^2049%4099=1), r_mod2049]
  rw [←Nat.powMod_def]
  decide

private theorem geo_exact (a r:Nat) (ha:9≤a) :
    (a-9)*geo a 9 r + 9^r = a^r := by
  induction r with
  | zero => simp [geo]
  | succ r ih =>
    have he : a-9+9=a := by omega
    calc
      (a-9)*geo a 9 (r+1)+9^(r+1)
          = (a-9)*(a*geo a 9 r+9^r)+9*9^r := by
              rw [geo, Nat.pow_succ]
              ac_rfl
      _ = (a-9)*a*geo a 9 r + ((a-9)+9)*9^r := by
            simp only [Nat.mul_add,Nat.add_mul]
            ac_rfl
      _ = a*((a-9)*geo a 9 r+9^r) := by
            rw [he]
            simp only [Nat.mul_add]
            ac_rfl
      _ = a*a^r := by rw [ih]
      _ = a^(r+1) := by rw [Nat.pow_succ]; ac_rfl

/-- The 11-valuation residue criterion holds on an infinite refinement
    of the four-parent cancellation-feeder progression. -/
theorem sourceB_mod4099 (t:Nat) : sourceB (idx t)%4099=2059 := by
  let r:=idx t
  let A:=xb r
  let G:=geo (A^2) 9 r
  have hr :1≤r := by dsimp [r,idx]; omega
  have hv : 6≤v r := by
    have hp : 9≤9^r := by
      have h :(9:Nat)^1≤9^r := Nat.pow_le_pow_right (by decide) hr
      simpa using h
    dsimp [v]; omega
  have hxb : 128≤A := by
    dsimp [A,xb]
    have h :(2:Nat)^7≤2^(v r+1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hbig : 9≤A^2 := by
    have hh : 3≤A := by omega
    have h : 3*3≤A*A := Nat.mul_le_mul hh hh
    simpa [Nat.pow_succ] using h
  have hA : A%4099=48 := xb_mod4099 t
  have hA2 : (A^2)%4099=2304 := by
    rw [Nat.pow_mod,hA]
  have hdiff : (A^2-9)%4099=2295 := by omega
  have hgeo := geo_exact (A^2) r hbig
  have h9 :9^r%4099=2955 := ninepow_mod4099 t
  have hpow : (A^2)^r%4099=2719 := A2pow_mod4099 t
  have hmod := congrArg (fun n:Nat=>n%4099) hgeo
  rw [Nat.add_mod,Nat.mul_mod,hdiff,h9,hpow] at hmod
  have hG : G%4099=909 := by
    dsimp [G]
    omega
  have hP : ((A-3)*G)%4099=4014 := by
    have hA3 : (A-3)%4099=45 := by omega
    rw [Nat.mul_mod,hA3,hG]
  have hv24 : 2^(v r)%4099=24 := two_mod4099 t
  change (2^(v r)*(A-3)*G)%4099=2059
  have hmul : 2^(v r)*(A-3)*G = 2^(v r)*((A-3)*G) := by ac_rfl
  rw [hmul, Nat.mul_mod, hv24,hP]

#print axioms sourceB_mod4099
end CancellationEleven
