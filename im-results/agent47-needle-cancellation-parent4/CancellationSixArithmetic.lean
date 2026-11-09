import NeedleCancelMod35
import Lean.Elab.Tactic.Omega

namespace CancellationSix
open NeedleCancelMod35

private theorem cycle131 (n : Nat) :
    2^n %131 = 2^(n%130)%131 := by
  have hr : 130*(n/130)+n%130=n := by
    have hh := Nat.mod_add_div n 130
    omega
  have hp : (2^(130*(n/130)))%131=1 := by
    rw [Nat.pow_mul, Nat.pow_mod, show (2:Nat)^130%131=1 by decide]
    simp
  calc
    (2^n)%131 = (2^(130*(n/130)+n%130))%131 := by rw [hr]
    _ = (2^(n%130))%131 := by
      rw [Nat.pow_add, Nat.mul_mod,hp]
      omega

private theorem nine_mod260 (n : Nat) : 9^(6*n+1)%260=9 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [show 6*(n+1)+1=(6*n+1)+6 by omega, Nat.pow_add,
          Nat.mul_mod, ih]

private theorem v_mod130 (t : Nat) : v (64069+1685970*t)%130=6 := by
  have hh := nine_mod260 (10678+280995*t)
  have he : 6*(10678+280995*t)+1=64069+1685970*t := by omega
  rw [he] at hh
  unfold v
  omega

private theorem xb_mod131 (t : Nat) : xb (64069+1685970*t)%131=128 := by
  unfold xb
  rw [cycle131]
  have h := v_mod130 t
  have he : (v (64069+1685970*t)+1)%130=7 := by omega
  rw [he]

private theorem geo131 (a r : Nat) (ha : a%131=9) :
    geo a 9 (r+1)%131=((r+1)*9^r)%131 := by
  induction r with
  | zero => simp [geo]
  | succ r ih =>
      calc
        geo a 9 (r+1+1)%131 =
            (a*geo a 9 (r+1)+9^(r+1))%131 := by rfl
        _ = (9*((r+1)*9^r)+9^(r+1))%131 := by
          rw [Nat.add_mod, Nat.mul_mod, ha, ih]
          simp [Nat.add_mod, Nat.mul_mod]
        _ = ((r+1+1)*9^(r+1))%131 := by
          rw [Nat.pow_succ]
          simp only [Nat.add_mul, Nat.mul_add]
          ac_rfl

theorem sourceB_mod131 (t : Nat) :
    sourceB (64069+1685970*t)%131=70 := by
  let r:=64069+1685970*t
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hv : v r%130=6 := v_mod130 t
  have hpow : 2^(v r)%131=64 := by
    rw [cycle131, hv]
  have hx : xb r%131=128 := xb_mod131 t
  have hXbig : 3≤xb r := by
    unfold xb
    have hval : 6≤v r := by
      have hp : (9:Nat)^1≤9^r := Nat.pow_le_pow_right (by decide) hr
      dsimp [v]
      omega
    have hh : (2:Nat)^7≤2^(v r+1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hsub : (xb r-3)%131=125 := by omega
  have hsq : ((xb r)^2)%131=9 := by
    rw [Nat.pow_mod, hx]
  have hg : (geo ((xb r)^2) 9 r)%131 = (r*9^(r-1))%131 := by
    have h := geo131 ((xb r)^2) (r-1) hsq
    have he : r-1+1=r := by omega
    rw [he] at h
    exact h
  have hnine : 9^r%131=7 := by
    have hcycle : 9^r%131=9^(r%65)%131 := by
      have hre :65*(r/65)+r%65=r := by
        have hh := Nat.mod_add_div r 65
        omega
      have hp : (9^(65*(r/65)))%131=1 := by
        rw [Nat.pow_mul,Nat.pow_mod,show (9:Nat)^65%131=1 by decide]
        simp
      calc
        9^r%131 = 9^(65*(r/65)+r%65)%131 := by rw [hre]
        _ = 9^(r%65)%131 := by
          rw [Nat.pow_add,Nat.mul_mod,hp]
          omega
    have hr65 :r%65=44 := by dsimp [r]; omega
    rw [hcycle,hr65]
  have hr131 : r%131=10 := by dsimp [r]; omega
  have htarget : (r*9^r)%131=70 := by
    rw [Nat.mul_mod,hr131,hnine]
  have hsource : sourceB r%131=(64*125*(r*9^(r-1)))%131 := by
    unfold sourceB
    simp [Nat.mul_mod, hpow, hsub, hg]
  have hgeom : (64*125*(r*9^(r-1)))%131=(r*9^r)%131 := by
    have hc : (64*125)%131=9 := by decide
    calc
      (64*125*(r*9^(r-1)))%131 = (9*(r*9^(r-1)))%131 := by
        simp [Nat.mul_mod, hc]
      _ = (r*(9^(r-1)*9))%131 := by ac_rfl
      _ = (r*9^r)%131 := by
        have he : r-1+1=r := by omega
        rw [←Nat.pow_succ, Nat.succ_eq_add_one, he]
  rw [hsource,hgeom,htarget]

#print axioms sourceB_mod131
end CancellationSix
