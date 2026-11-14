import CancellationTopStrip
import Lean.Elab.Tactic.Omega

/-!
A kernel-checkable arithmetic core for the all-r cancellation-feeder
middle-band inverse-parent exclusion.  The first formalization uses the
slightly coarser threshold 4*r-3; the paper note's sharper
1 + floor(log2(3^(2*r-1))) threshold is a later strengthening target.
-/

namespace CancellationMidBandCoarse

open CancellationNat CancellationGap CancellationStrip

def geomSum (t : Nat) : Nat → Nat
  | 0 => 0
  | r+1 => geomSum t r + t^(2*r) + t^(2*r+1)

def certificateC (A t : Nat) : Nat → Nat
  | 0 => 0
  | r+1 =>
      (A*t)^2 * certificateC A t r
        + 3^(2*r) * (A*t-3) * geomSum t r
        + 9^r * t^(2*r) * (t*(A-3)-3)

theorem factor_square (B : Nat) (hB : 3 ≤ B) :
    B*B = 9 + (B+3)*(B-3) := by
  let x := B-3
  have hx : B = x+3 := by dsimp [x]; omega
  have hxs : B-3=x := by dsimp [x]; rfl
  rw [hx,hxs]
  simp only [Nat.add_mul,Nat.mul_add]
  omega

theorem factor_shift (A t : Nat) (hA : 8 ≤ A) (ht : 2 ≤ t) :
    t*t*A*(A-3) =
      9*(1+t) + (A*t+3)*(t*(A-3)-3) := by
  have hA3 : 3 ≤ A := by omega
  have hX3 : 3 ≤ t*(A-3) := by
    have hA5 : 5 ≤ A-3 := by omega
    have hmul := Nat.mul_le_mul ht hA5
    omega
  let x := t*(A-3)-3
  have hx : t*(A-3)=x+3 := by dsimp [x]; omega
  have hB : A*t=x+3+3*t := by
    calc
      A*t = (A-3+3)*t := by rw [Nat.sub_add_cancel hA3]
      _ = (A-3)*t+3*t := by rw [Nat.add_mul]
      _ = t*(A-3)+3*t := by ac_rfl
      _ = x+3+3*t := by rw [hx]
  have hleft : t*t*A*(A-3)=(x+3+3*t)*(x+3) := by
    calc
      t*t*A*(A-3) = (A*t)*(t*(A-3)) := by ac_rfl
      _ = (x+3+3*t)*(x+3) := by rw [hB,hx]
  have hright :
      9*(1+t)+(A*t+3)*(t*(A-3)-3)
        = 9*(1+t)+(x+3+3*t+3)*x := by
    rw [hB,hx]
    rfl
  rw [hleft,hright]
  simp only [Nat.add_mul,Nat.mul_add]
  omega

/-- Exact natural-number quotient certificate for the recurrence. -/
theorem certificate_identity (A t r : Nat)
    (hA : 8 ≤ A) (ht : 2 ≤ t) :
    t^(2*r)*A*P A r =
      3^(2*r)*geomSum t r + (A*t+3)*certificateC A t r := by
  induction r with
  | zero =>
      simp [P,geomSum,certificateC]
  | succ r ih =>
      let B := A*t
      let X := t*(A-3)
      have hB3 : 3 ≤ B := by dsimp [B]; omega
      have hBfactor : B*B=9+(B+3)*(B-3) :=
        factor_square B hB3
      have hXfactor :
          t*t*A*(A-3)=9*(1+t)+(B+3)*(X-3) := by
        simpa [B,X] using factor_shift A t hA ht
      have htPow : t^(2*r+2)=t^(2*r)*(t*t) := by
        rw [Nat.pow_add]
        simp
      have h3Pow : 3^(2*r+2)=9*3^(2*r) := by
        rw [Nat.pow_add]
        rw [show (3:Nat)^2=9 by decide]
        ac_rfl
      have hL :
          t^(2*r+2)*A*(A*A*P A r+9^r*(A-3))
            = B^2*(t^(2*r)*A*P A r)
                + 9^r*t^(2*r)*t*t*A*(A-3) := by
        rw [htPow]
        simp only [Nat.mul_add]
        dsimp [B]
        ac_rfl
      have hR :
          3^(2*r+2)*(geomSum t r+t^(2*r)+t^(2*r+1))
            + (B+3)*(B^2*certificateC A t r
                + 3^(2*r)*(B-3)*geomSum t r
                + 9^r*t^(2*r)*(X-3))
            =
          B^2*(3^(2*r)*geomSum t r+(B+3)*certificateC A t r)
            + 9^r*t^(2*r)*t*t*A*(A-3) := by
        rw [h3Pow,hBfactor,hXfactor]
        simp only [Nat.add_mul,Nat.mul_add]
        omega
      change t^(2*r+2)*A*(A*A*P A r+9^r*(A-3)) =
        3^(2*r+2)*(geomSum t r+t^(2*r)+t^(2*r+1))
          + (A*t+3)*((A*t)^2*certificateC A t r
              + 3^(2*r)*(A*t-3)*geomSum t r
              + 9^r*t^(2*r)*(t*(A-3)-3))
      calc
        t^(2*r+2)*A*(A*A*P A r+9^r*(A-3))
            = B^2*(t^(2*r)*A*P A r)
                + 9^r*t^(2*r)*t*t*A*(A-3) := hL
        _ = B^2*(3^(2*r)*geomSum t r+(B+3)*certificateC A t r)
                + 9^r*t^(2*r)*t*t*A*(A-3) := by rw [ih]
        _ = 3^(2*r+2)*(geomSum t r+t^(2*r)+t^(2*r+1))
              + (B+3)*(B^2*certificateC A t r
                  + 3^(2*r)*(B-3)*geomSum t r
                  + 9^r*t^(2*r)*(X-3)) := hR.symm

/-- For r>=2, the coarse threshold 4r-3 already lies above
    3^(2r-1) by a margin of five. -/
theorem coarse_threshold (r : Nat) (hr : 2 ≤ r) :
    3^(2*r-1)+5 ≤ 2^(4*r-3) := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => decide
    | succ r =>
      induction r with
      | zero => decide
      | succ r ih =>
        have hpow2 :
            2^(4*(r+3)-3)=16*2^(4*(r+2)-3) := by
          rw [show 4*(r+3)-3=(4*(r+2)-3)+4 by omega, Nat.pow_add]
          decide
        have hpow3 :
            3^(2*(r+3)-1)=9*3^(2*(r+2)-1) := by
          rw [show 2*(r+3)-1=(2*(r+2)-1)+2 by omega, Nat.pow_add]
          decide
        rw [hpow2,hpow3]
        omega

/-- The finite geometric sum is just below its leading power by the
    exact quotient identity, with no rational arithmetic. -/
theorem geomSum_identity (t r : Nat) (ht : 1 ≤ t) :
    (t-1)*geomSum t r + 1 = t^(2*r) := by
  induction r with
  | zero =>
      simp [geomSum]
  | succ r ih =>
      have hsub : t-1+1=t := Nat.sub_add_cancel ht
      have hfirst : t^(2*r)+(t-1)*t^(2*r)=t^(2*r+1) := by
        calc
          t^(2*r)+(t-1)*t^(2*r)
              = ((t-1)+1)*t^(2*r) := by
                  rw [Nat.add_mul]
                  ac_rfl
          _ = t*t^(2*r) := by rw [hsub]
          _ = t^(2*r+1) := by rw [Nat.pow_succ']; rfl
      have hsecond :
          t^(2*r+1)+(t-1)*t^(2*r+1)=t^(2*r+2) := by
        calc
          t^(2*r+1)+(t-1)*t^(2*r+1)
              = ((t-1)+1)*t^(2*r+1) := by
                  rw [Nat.add_mul]
                  ac_rfl
          _ = t*t^(2*r+1) := by rw [hsub]
          _ = t^(2*r+2) := by rw [Nat.pow_succ']; rfl
      change (t-1)*(geomSum t r+t^(2*r)+t^(2*r+1))+1
        = t^(2*r+2)
      rw [Nat.mul_add,Nat.mul_add]
      calc
        (t-1)*geomSum t r+(t-1)*t^(2*r)
            +(t-1)*t^(2*r+1)+1
            = ((t-1)*geomSum t r+1)
                +(t-1)*t^(2*r)+(t-1)*t^(2*r+1) := by omega
        _ = t^(2*r)+(t-1)*t^(2*r)+(t-1)*t^(2*r+1) := by rw [ih]
        _ = t^(2*r+2) := by rw [hfirst,hsecond]

/-- If 2^s is at least n+5, then the geometric tail has quotient
    strictly less than n+1. -/
theorem geom_bound (r s n : Nat) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hnq : n+5 ≤ 2^s) :
    n*geomSum (2^s) r < (n+1)*2^((2*r-1)*s) := by
  let q := 2^s
  let T := 2^((2*r-1)*s)
  have hq : 1 ≤ q := by dsimp [q]; exact Nat.one_le_pow s 2 (by decide)
  have hT : 0 < T := by dsimp [T]; exact Nat.pow_pos (by decide)
  have hgeom := geomSum_identity q r hq
  have hqT : q*T=q^(2*r) := by
    dsimp [q,T]
    rw [←Nat.pow_add]
    congr 1
    omega
  have hS : (q-1)*geomSum q r < q*T := by
    have heq : (q-1)*geomSum q r+1=q*T := by
      rw [hgeom,hqT]
    omega
  have hqminus : n < q-1 := by
    dsimp [q] at hnq
    omega
  have hqprod : n*q < (n+1)*(q-1) := by
    have hqpos : 1 ≤ q := by omega
    calc
      n*q = n*((q-1)+1) := by rw [Nat.sub_add_cancel hqpos]
      _ = n*(q-1)+n := by rw [Nat.mul_add]; omega
      _ < (n+1)*(q-1) := by
        rw [Nat.add_mul]
        exact Nat.add_lt_add_left hqminus _
  have hprod1 :
      n*((q-1)*geomSum q r) < n*(q*T) :=
    Nat.mul_lt_mul_of_pos_left hS (by omega)
  have hprod2 :
      (n*q)*T < ((n+1)*(q-1))*T :=
    Nat.mul_lt_mul_of_pos_right hqprod hT
  have hprod :
      (n*geomSum q r)*(q-1) < ((n+1)*T)*(q-1) := by
    calc
      (n*geomSum q r)*(q-1) = n*((q-1)*geomSum q r) := by ac_rfl
      _ < n*(q*T) := hprod1
      _ = (n*q)*T := by ac_rfl
      _ < ((n+1)*(q-1))*T := hprod2
      _ = ((n+1)*T)*(q-1) := by ac_rfl
  have hfinal : n*geomSum q r < (n+1)*T := by
    by_contra hnot
    have hle : (n+1)*T ≤ n*geomSum q r := by omega
    have hmul := Nat.mul_le_mul_right (q-1) hle
    omega
  simpa [q,T] using hfinal

#print axioms certificate_identity
#print axioms coarse_threshold
#print axioms geomSum_identity
#print axioms geom_bound

end CancellationMidBandCoarse
