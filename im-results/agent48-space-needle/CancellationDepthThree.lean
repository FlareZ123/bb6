import CancellationDepthTwo
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace NeedleCancelDepthThree
open NeedleCancelMod35

private theorem nine_mod840_shift30 (t : Nat) : 9^(30*t+4)%840=681 := by
  induction t with
  | zero => decide
  | succ t ih =>
      have he : 9^(30*(t+1)+4)=9^(30*t+4)*9^30 := by
        rw [show 30*(t+1)+4=(30*t+4)+30 by omega, Nat.pow_add]
      rw [he, Nat.mul_mod, ih]

private theorem v_mod420_30t4 (t : Nat) :
    v (30*t+4)%420=342 := by
  have h:=nine_mod840_shift30 t
  dsimp [v]
  omega

private theorem pow2_period420 (n : Nat) :
    2^n%1225 = 2^(n%420)%1225 := by
  have hrep : n=420*(n/420)+n%420 := by omega
  calc
    2^n%1225=2^(420*(n/420)+n%420)%1225 := by rw [←hrep]
    _=2^(n%420)%1225 := by
      rw [Nat.pow_add,Nat.pow_mul,Nat.mul_mod]
      have h420 : 2^420%1225=1 := by decide
      simp [Nat.pow_mod,h420]

private theorem geo_congr (a b c d n m : Nat)
    (ha : a%m=c%m) (hb : b%m=d%m) :
    geo a b n%m=geo c d n%m := by
  induction n with
  | zero => simp [geo]
  | succ n ih =>
      simp only [geo]
      rw [Nat.add_mod, Nat.mul_mod, ha,ih]
      have hp : b^n%m=d^n%m := by
        rw [Nat.pow_mod]
        simp only [hb]
        rw [←Nat.pow_mod]
      rw [hp]
      simp [Nat.add_mod,Nat.mul_mod]

private theorem geo_add (a b n m : Nat) :
    geo a b (n+m) = a^m*geo a b n + b^n*geo a b m := by
  induction m with
  | zero => simp [geo]
  | succ m ih =>
      rw [Nat.add_succ]
      simp only [geo, ih, Nat.pow_succ]
      simp [Nat.pow_add, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem geo_shift30 (n : Nat) :
    geo 214 9 (n+30) = 214^30*geo 214 9 n + 9^n*geo 214 9 30 :=
  geo_add _ _ _ _

private theorem nine_r_mod7 (t:Nat):9^(30*t+4)%7=2 := by
  have he : 9^(30*t+4)%7=2^((30*t+4)%3)%7 := by
    rw [Nat.pow_mod]
    have h9 : 9%7=2 := by decide
    rw [h9]
    have h3:2^3%7=1:=by decide
    have hrep : 30*t+4=3*((30*t+4)/3)+(30*t+4)%3 := by omega
    rw [show 2^(30*t+4) = 2^(3*((30*t+4)/3)+(30*t+4)%3) by rw [←hrep]]
    rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
    simp [Nat.pow_mod,h3]
  rw [he]
  have hm : (30*t+4)%3=1 := by omega
  rw [hm]

private theorem geo_30t4_mod245 (t : Nat) :
    geo 214 9 (30*t+4)%245=(106+70*t)%245 := by
  induction t with
  | zero => decide
  | succ t ih =>
      have hshift := geo_shift30 (30*t+4)
      have hpow : 214^30%245=1 := by decide
      have hbase : geo 214 9 30%245=35 := by decide
      have h9 := nine_r_mod7 t
      have h9mod : (9^(30*t+4)*35)%245=70 := by
        have hfactor : 35*(9^(30*t+4)%7) = (9^(30*t+4)*35)%245 := by omega
        omega
      have hterm : (9^(30*t+4)*geo 214 9 30)%245=70 := by
        calc
          _ = ((9^(30*t+4)%245)*(geo 214 9 30%245))%245 := by rw [Nat.mul_mod]
          _ = ((9^(30*t+4)%245)*35)%245 := by rw [hbase]
          _ = (9^(30*t+4)*35)%245 := by rw [Nat.mul_mod]; simp
          _ = 70 := h9mod
      have he : 30*(t+1)+4=(30*t+4)+30 := by omega
      rw [he,hshift,Nat.add_mod,Nat.mul_mod,hpow,ih,hterm]
      omega

private theorem sourceB_30t4_mod1225 (t : Nat) :
    sourceB (30*t+4)%1225=(545+175*t)%1225 := by
  let r:=30*t+4
  have hv:=v_mod420_30t4 t
  have hv1 : (v r+1)%420=343 := by simpa [r] using (show (v (30*t+4)+1)%420=343 by omega)
  have hy : 2^(v r)%1225=554 := by rw [pow2_period420,hv]; decide
  have hx : xb r%1225=1108 := by
    unfold xb
    rw [pow2_period420,hv1]
    decide
  have hlarge : 3≤xb r := by
    have hr : 1≤r := by dsimp [r]; omega
    have h9 : 9≤9^r := by simpa using (Nat.pow_le_pow_right (by decide : 0<(9:Nat)) hr : 9^1≤9^r)
    have hv6 : 6≤v r := by dsimp [v]; omega
    have hp : 2^7≤2^(v r+1) := Nat.pow_le_pow_right (by decide) (by omega)
    dsimp [xb]
    omega
  have hsub : (xb r-3)%1225=1105 := by omega
  have hsq : (xb r)^2%245=214 := by
    have hx245 : xb r%245=128 := by omega
    rw [Nat.pow_mod,hx245]
  have hg : geo ((xb r)^2) 9 r%245=geo 214 9 r%245 :=
    geo_congr _ _ _ _ _ _ hsq (by decide)
  have ht : geo 214 9 r%245=(106+70*t)%245 :=
    geo_30t4_mod245 t
  have hgm : geo ((xb r)^2) 9 r%245=(106+70*t)%245 := by omega
  have hprod : (2^(v r)*(xb r-3))%1225=895 := by
    rw [Nat.mul_mod,hy,hsub]
  have hreduce : (895*geo ((xb r)^2) 9 r)%1225=
      (895*(geo ((xb r)^2) 9 r%245))%1225 := by
    omega
  unfold sourceB
  calc
    _ = (((2^(v r)*(xb r-3))%1225)*(geo ((xb r)^2) 9 r%1225))%1225 := by
      rw [Nat.mul_mod]
    _ = (895*geo ((xb r)^2) 9 r)%1225 := by rw [hprod]; omega
    _ = (895*(geo ((xb r)^2) 9 r%245))%1225 := hreduce
    _ = (895*((106+70*t)%245))%1225 := by rw [hgm]
    _ = (545+175*t)%1225 := by omega

/-- A valuation-one, then zero, then four inverse arithmetic signature. -/
theorem cancellation_one_zero_four_residue (r:Nat) (hr:1≤r) :
    sourceB r%1225=545 ↔ r%210=4 := by
  constructor
  · intro hb
    have hb175 : sourceB r%175=20 := by omega
    have hr30 := (NeedleCancelDepthTwo.cancellation_four_then_zero_residue r hr).mp hb175
    have hrepr : r=30*(r/30)+4 := by omega
    have ht := sourceB_30t4_mod1225 (r/30)
    rw [←hrepr] at ht
    have ht7 : (r/30)%7=0 := by omega
    omega
  · intro hr210
    have hr30 : r%30=4 := by omega
    have hrepr : r=30*(r/30)+4 := by omega
    have ht7 : (r/30)%7=0 := by omega
    have ht := sourceB_30t4_mod1225 (r/30)
    rw [←hrepr] at ht
    omega

#print axioms cancellation_one_zero_four_residue
end NeedleCancelDepthThree
