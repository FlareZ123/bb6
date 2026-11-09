import Std
import Lean.Elab.Tactic.Omega

namespace NeedleCancelMod35

/-- Cancellation valuation and its shifted exponential base. -/
def v (r : Nat) := (9^r+3)/2
def geo (a b : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => a * geo a b n + b^n

def xb (r : Nat) := 2^(v r+1)
def sourceB (r : Nat) : Nat := 2^(v r) * (xb r-3) * geo ((xb r)^2) 9 r

theorem nine_mod24 (n : Nat) : 9^(n+1)%24=9 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : 9^(n+1+1)=9^(n+1)*9 := by rw [Nat.pow_succ]
      rw [hpow, Nat.mul_mod, ih]

theorem v_mod12 (r : Nat) (hr : 1≤r) : v r %12=6 := by
  have h : 9^r%24=9 := by
    have he:r=(r-1)+1:=by omega
    rw [he]
    exact nine_mod24 (r-1)
  dsimp [v]
  omega

theorem two_pow_mod7 (n : Nat) (hn : n%3=0) : 2^n%7=1 := by
  have hh : n=3*(n/3) := by omega
  rw [hh, Nat.pow_mul]
  simp [show (2:Nat)^3=8 by decide, Nat.pow_mod]

theorem two_pow_mod5 (n : Nat) (hn : n%4=2) : 2^(n+1)%5=3 := by
  have hh:n=4*(n/4)+2 := by omega
  rw [hh]
  have he:4*(n/4)+2+1=4*(n/4)+3:=by omega
  rw [he, Nat.pow_add, Nat.pow_mul]
  simp [show (2:Nat)^4=16 by decide, Nat.pow_mod, Nat.mul_mod]

theorem geo_period3 (n : Nat) : geo 4 2 (n+3)%7 = geo 4 2 n%7 := by
  have hn1 : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
  have hn2 : 2^(n+2)=4*2^n := by
    rw [show n+2=(n+1)+1 by omega, Nat.pow_succ, hn1]
    omega
  have he : geo 4 2 (n+3)=64*geo 4 2 n+28*2^n := by
    simp only [geo]
    rw [hn1, hn2]
    omega
  rw [he]
  omega

theorem geo31 (t : Nat) : geo 4 2 (3*t+1)%7=1 := by
  induction t with
  | zero => decide
  | succ t ih =>
      have hs : 3*(t+1)+1=(3*t+1)+3 := by omega
      rw [hs, geo_period3]
      exact ih

theorem geo_mod7_congr (a b n:Nat)
    (ha:a%7=4) (hb:b%7=2) :
    (geo a b n)%7=(geo 4 2 n)%7 := by
  induction n with
  | zero => simp [geo]
  | succ n ih =>
      simp only [geo]
      rw [Nat.add_mod, Nat.mul_mod, ha, ih]
      have hbpow : b^n%7=2^n%7 := by
        rw [Nat.pow_mod]
        simp only [hb]
      rw [hbpow]
      simp [Nat.add_mod, Nat.mul_mod]

/-- Every r=3*t+1 cancellation-family target has residue 20 modulo 35. -/
theorem sourceB_mod35 (t : Nat) : sourceB (3*t+1)%35=20 := by
  let r:=3*t+1
  have hr : 1≤r := by omega
  have hv12 : v r%12=6 := v_mod12 r hr
  have hv3 : v r%3=0 := by omega
  have hv4 : v r%4=2 := by omega
  have hy7 : 2^(v r)%7=1 := two_pow_mod7 (v r) hv3
  have hX7 : xb r%7=2 := by
    unfold xb
    rw [Nat.pow_succ, Nat.mul_mod, hy7]
  have hX5 : xb r%5=3 := by
    unfold xb
    exact two_pow_mod5 (v r) hv4
  have hXbig : 3≤xb r := by
    unfold xb
    have hpositive : 1≤v r := by omega
    have hpow : (2:Nat)^2 ≤2^(v r+1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hsub7 : (xb r-3)%7=6 := by omega
  have hsub5 : (xb r-3)%5=0 := by omega
  have ha7 : ((xb r)^2)%7=4 := by
    rw [Nat.pow_mod,hX7]
  have hb7 : 9%7=2 := by decide
  have hgeo7 : (geo ((xb r)^2) 9 r)%7=1 := by
    rw [geo_mod7_congr ((xb r)^2) 9 r ha7 hb7]
    change (geo 4 2 (3*t+1))%7=1
    exact geo31 t
  have hsource5 : sourceB r %5 =0 := by
    simp [sourceB, Nat.mul_mod, hsub5]
  have hsource7 : sourceB r%7=6 := by
    simp [sourceB, Nat.mul_mod, hy7, hsub7, hgeo7]
  have hresult : sourceB r%35=20 := by omega
  simpa [r] using hresult

#print axioms sourceB_mod35
end NeedleCancelMod35
