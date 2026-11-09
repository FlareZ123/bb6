import NeedleCancelMod35
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace NeedleCancelDepthTwo
open NeedleCancelMod35

private theorem nine_odd_mod120 (t : Nat) : 9^(2*t+1)%120=9 := by
  induction t with
  | zero => decide
  | succ t ih =>
      have he : 9^(2*(t+1)+1)=9^(2*t+1)*81 := by
        rw [show 2*(t+1)+1=(2*t+1)+2 by omega, Nat.pow_add]
      rw [he,Nat.mul_mod,ih]

private theorem nine_even_mod120 (t : Nat) : 9^(2*t+2)%120=81 := by
  induction t with
  | zero => decide
  | succ t ih =>
      have he : 9^(2*(t+1)+2)=9^(2*t+2)*81 := by
        rw [show 2*(t+1)+2=(2*t+2)+2 by omega,Nat.pow_add]
      rw [he,Nat.mul_mod,ih]

private theorem v_odd_mod60 (r : Nat) (h : r%2=1) : v r%60=6 := by
  have hre : r=2*(r/2)+1 := by omega
  have hp : 9^r%120=9 := by rw [hre]; exact nine_odd_mod120 _
  dsimp [v]
  omega

private theorem v_even_mod60 (r : Nat) (hr : 1≤r) (h : r%2=0) :
    v r%60=42 := by
  have hre : r=2*(r/2-1)+2 := by omega
  have hp : 9^r%120=81 := by rw [hre]; exact nine_even_mod120 _
  dsimp [v]
  omega

private theorem pow2_mod175 (n : Nat) :
    2^n%175 = 2^(n%60)%175 := by
  have hrep : n=60*(n/60)+n%60 := by omega
  calc
    2^n%175 = 2^(60*(n/60)+n%60)%175 := by rw [←hrep]
    _ = 2^(n%60)%175 := by
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
      have h60 : 2^60%175=1 := by decide
      simp [Nat.pow_mod,h60]

private theorem geo_congr_mod (a b c d n m : Nat)
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
      simp [Nat.add_mod, Nat.mul_mod]

private theorem four_even_mod5 (t : Nat) : 4^(2*t)%5=1 := by
  rw [Nat.pow_mul]
  simp [Nat.pow_mod]

private theorem geo44_even_mod5 (t : Nat) :
    geo 4 4 (2*t)%5=(3*t)%5 := by
  induction t with
  | zero => decide
  | succ t ih =>
      have he : geo 4 4 (2*(t+1)) =
          16*geo 4 4 (2*t)+8*4^(2*t) := by
        rw [show 2*(t+1)=(2*t+1)+1 by omega]
        simp only [geo]
        rw [Nat.pow_succ]
        omega
      have hp := four_even_mod5 t
      have hterm : (8*4^(2*t))%5=3 := by
        rw [Nat.mul_mod,hp]
      calc
        _ = (16*geo 4 4 (2*t)+8*4^(2*t))%5 := by rw [he]
        _ = (((16*geo 4 4 (2*t))%5)+((8*4^(2*t))%5))%5 := by rw [Nat.add_mod]
        _ = ((3*t)%5+3)%5 := by
          rw [Nat.mul_mod,ih,hterm]
          omega
        _ = (3*(t+1))%5 := by omega

private theorem sourceB_large (r : Nat) (hr : 1≤r) : 3≤xb r := by
  have h9 : 9≤9^r := by
    simpa using (Nat.pow_le_pow_right (by decide : 0<(9:Nat)) hr : 9^1≤9^r)
  have hv : 6≤v r := by dsimp [v]; omega
  have hp : 2^7≤2^(v r+1) := Nat.pow_le_pow_right (by decide) (by omega)
  dsimp [xb]
  omega

private theorem sourceB_even_mod175 (r : Nat) (hr : 1≤r)
    (heven : r%2=0) :
    sourceB r%175 = (20*geo ((xb r)^2) 9 r)%175 := by
  have hv := v_even_mod60 r hr heven
  have hv1 : (v r+1)%60=43 := by omega
  have hy : 2^(v r)%175=29 := by rw [pow2_mod175,hv]
  have hxb : xb r%175=58 := by
    unfold xb
    rw [pow2_mod175,hv1]
  have hlarge := sourceB_large r hr
  have hsub : (xb r-3)%175=55 := by omega
  have hm : (2^(v r)*(xb r-3))%175=(29*55)%175 := by
    rw [Nat.mul_mod,hy,hsub]
  unfold sourceB
  calc
    _ = (((2^(v r)*(xb r-3))%175)*(geo ((xb r)^2) 9 r%175))%175 := by
      rw [Nat.mul_mod]
    _ = (((29*55)%175)*(geo ((xb r)^2) 9 r%175))%175 := by rw [hm]
    _ = (20*geo ((xb r)^2) 9 r)%175 := by omega

private theorem sourceB_odd_mod175 (r : Nat) (hodd : r%2=1) :
    sourceB r%175 = (125*geo ((xb r)^2) 9 r)%175 := by
  have hv := v_odd_mod60 r hodd
  have hv1 : (v r+1)%60=7 := by omega
  have hy : 2^(v r)%175=64 := by rw [pow2_mod175,hv]
  have hxb : xb r%175=128 := by
    unfold xb
    rw [pow2_mod175,hv1]
  have hr : 1≤r := by omega
  have hlarge := sourceB_large r hr
  have hsub : (xb r-3)%175=125 := by omega
  have hm : (2^(v r)*(xb r-3))%175=(64*125)%175 := by
    rw [Nat.mul_mod,hy,hsub]
  unfold sourceB
  calc
    _ = (((2^(v r)*(xb r-3))%175)*(geo ((xb r)^2) 9 r%175))%175 := by
      rw [Nat.mul_mod]
    _ = (((64*125)%175)*(geo ((xb r)^2) 9 r%175))%175 := by rw [hm]
    _ = (125*geo ((xb r)^2) 9 r)%175 := by omega

private theorem geo_source_even_mod5 (r : Nat) (hr : 1≤r)
    (heven : r%2=0) :
    geo ((xb r)^2) 9 r%5 = (3*(r/2))%5 := by
  have hv := v_even_mod60 r hr heven
  have hv1 : (v r+1)%60=43 := by omega
  have hxb : xb r%175=58 := by
    unfold xb
    rw [pow2_mod175,hv1]
  have hxb5 : xb r%5=3 := by omega
  have hsq : (xb r)^2%5=4 := by rw [Nat.pow_mod,hxb5]
  have hg := geo_congr_mod ((xb r)^2) 9 4 4 r 5 hsq (by decide)
  have hre : r=2*(r/2) := by omega
  calc
    _ = geo 4 4 r%5 := hg
    _ = geo 4 4 (2*(r/2))%5 := by rw [←hre]
    _ = (3*(r/2))%5 := geo44_even_mod5 _

/-- An all-index, depth-two inverse congruence for the cancellation sources. -/
theorem cancellation_four_then_zero_residue (r : Nat) (hr : 1≤r) :
    sourceB r%175=20 ↔ r%30=4 := by
  constructor
  · intro hB
    have hB35 : sourceB r%35=20 := by omega
    have h3 : r%3=1 := (sourceB_mod35_iff r hr).mp hB35
    have hc : r%2=0 ∨ r%2=1 := by omega
    rcases hc with heven | hodd
    · have hg5 := geo_source_even_mod5 r hr heven
      have hBform := sourceB_even_mod175 r hr heven
      have hgeo5 : geo ((xb r)^2) 9 r%5=1 := by omega
      have ht : (r/2)%5=2 := by omega
      omega
    · have hBform := sourceB_odd_mod175 r hodd
      omega
  · intro h30
    have heven : r%2=0 := by omega
    have h3 : r%3=1 := by omega
    have hB35 : sourceB r%35=20 := (sourceB_mod35_iff r hr).mpr h3
    have hBform := sourceB_even_mod175 r hr heven
    have hg5 := geo_source_even_mod5 r hr heven
    have hgeo5 : geo ((xb r)^2) 9 r%5=1 := by omega
    omega

#print axioms cancellation_four_then_zero_residue
end NeedleCancelDepthTwo
