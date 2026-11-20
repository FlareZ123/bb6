import P2NextQ4TailBlankRight
import Lean.Elab.Tactic.Omega

/-!
# Exact left-residual update at the next P2 q4Tail input

The P2 postlude preserves its residual left tail, but the following
22-step prefix rewrites the first three cells of that tail to ones.
Thus the next q4Tail source residual is 111 ++ tail.drop 3, not merely
tail.drop 6.  In the authentic root specialization this is
111111 ++ tail0.drop 6, so the same 100-guard postlude cannot be
reapplied immediately.

This is a source-level coordinate theorem, not a halting theorem.  It
has not been locally compiled in the current invocation.
-/

namespace BB6Coverage.Agent42P2NextQ4TailLeftResidual

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent42Q4S0Drain
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent44P2Postlude
open BB6Coverage.Agent48PositiveZFirstCycle
open BB6Coverage.Agent48PositiveZFirstCyclePrefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent42P2NextQ4TailBlankRight

private theorem sideBit_drop_local
    (xs : List Bool) (k i : Nat) :
    sideBit (xs.drop k) i = sideBit xs (k+i) := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
      cases xs with
      | nil => simp [sideBit]
      | cons b xs =>
          have hidx : k+1+i=(k+i)+1 := by omega
          simpa [List.drop,sideBit,hidx] using ih xs

/-- The P2 postlude leaves the complete old residual tail at cells
-1,-2,... in nearest-first order. -/
private theorem p2PostludeFrame_left_tail_local
    (m n : Nat) (tail : List Bool) (hn : 2 ≤ n) (j : Nat) :
    (p2PostludeFrame m n tail).tape (-1-(j:Int)) =
      sideBit tail j := by
  let a : Nat := n-1
  let H : Int := (m+2+3*n)
  let K : Nat := 3*a+(m+2)
  let ell : List Bool := p2ResidualLeft m tail
  let T : Int → Bool := (s0Config ell a 0 (2^a-1) H).tape
  let U : Int → Bool := s0LeftSweep K T H
  have hcenter : H-(K:Int)=3 := by
    dsimp [H,K,a]
    omega
  have hk : 0<K := by
    dsimp [K,a]
    omega
  have hleft : s0LeftFacing ell a 0 = d1pow a ++ ell := by
    simp [s0LeftFacing,binDec_zero]
  have hcellTail (j : Nat) :
      T (-1-(j:Int)) = sideBit tail j := by
    have hc := s0Config_left_cell ell a 0 (2^a-1) H (K+4+j)
    change T (H-(K+4+j:Int)) =
      sideBit (s0LeftFacing ell a 0) (K+4+j) at hc
    rw [hleft] at hc
    rw [Agent6Q4Prefix.sideBit_append_right (d1pow a) ell
      (K+4+j) (by rw [d1pow_length]; dsimp [K]; omega)] at hc
    rw [d1pow_length] at hc
    have hidx1 : K+4+j-3*a=m+6+j := by
      dsimp [K]
      omega
    rw [hidx1] at hc
    rw [p2ResidualLeft] at hc
    rw [Agent6Q4Prefix.sideBit_append_right
      (List.replicate (m+2) true)
      ([false,true,false,false] ++ tail) (m+6+j) (by simp; omega)] at hc
    have hidx2 : m+6+j-(m+2)=4+j := by omega
    rw [hidx2] at hc
    rw [Agent6Q4Prefix.sideBit_append_right
      ([false,true,false,false] : List Bool) tail (4+j)
      (by simp; omega)] at hc
    have hidx3 : 4+j-4=j := by omega
    rw [hidx3] at hc
    have hcoord : H-(K+4+j:Int)=-1-(j:Int) := by omega
    rw [hcoord] at hc
    exact hc
  have hframe (x : Int) (hx : x≤-1) :
      (p2PostludeFrame m n tail).tape x = U x := by
    change (q4FrameAt U 3 q4S0Final4Inside q4S0Final4End).tape x = U x
    rw [q4FrameAt_tape]
    have hnot : q4S0Final4Inside (x-3)=false := by
      simp [q4S0Final4Inside]
      omega
    simp [hnot]
  have hsweep (x : Int) (hx : x≤3) : U x=T x := by
    rw [s0LeftSweep_shift]
    simp [hcenter,hx]
  calc
    (p2PostludeFrame m n tail).tape (-1-(j:Int)) =
        U (-1-(j:Int)) := hframe _ (by omega)
    _ = T (-1-(j:Int)) := hsweep _ (by omega)
    _ = sideBit tail j := hcellTail j

/-- The new left residual tail is the three-one prefix followed by the
old tail after its first three cells. -/
def p2NextQ4TailResidualTail (tail : List Bool) : List Bool :=
  [true,true,true] ++ tail.drop 3

/-- Pointwise left-ray identity at the next q4Tail source tape, before
the next d0 sweep. -/
theorem p2NextQ4Tail_leftResidual
    (m n : Nat) (tail : List Bool) (hn : 2 ≤ n) (j : Nat) :
    p2NextQ4TailInputTape m n tail (-1-(j:Int)) =
      sideBit (p2NextQ4TailResidualTail tail) j := by
  let H : Int := (m+2+3*n)
  let P := p2PostludeFrame m n tail
  let T1 := (frameAt P.tape 1
    firstCyclePrefix22Inside firstCyclePrefix22End).tape
  let h1 : Int := H+5
  let T2 := afterFirstCycleTwoZero T1 h1
  have hT2 : p2NextQ4TailInputTape m n tail = T2 := by
    rfl
  rw [hT2]
  let x : Int := -1-(j:Int)
  have hsetup : T2 x=T1 x := by
    have hne0 : x≠h1 := by dsimp [x,h1,H]; omega
    have hne1 : x≠h1+1 := by dsimp [x,h1,H]; omega
    simp [T2,afterFirstCycleTwoZero,hne0,hne1]
  by_cases hj : j<3
  · have hprefix : T1 x=true := by
      change (frameAt P.tape 1
        firstCyclePrefix22Inside firstCyclePrefix22End).tape x=true
      rw [frameAt_tape]
      have hinside : firstCyclePrefix22Inside (x-1)=true := by
        simp [firstCyclePrefix22Inside]
        dsimp [x]
        omega
      have hmark : x-1 ∈ firstCyclePrefix22End.marked := by
        dsimp [x]
        interval_cases j <;> norm_num [firstCyclePrefix22End]
      simp [hinside,hmark]
    have htarget :
        sideBit (p2NextQ4TailResidualTail tail) j=true := by
      unfold p2NextQ4TailResidualTail
      interval_cases j <;> simp [sideBit]
    calc
      T2 x = T1 x := hsetup
      _ = true := hprefix
      _ = sideBit (p2NextQ4TailResidualTail tail) j := htarget.symm
  · have hj3 : 3≤j := by omega
    have hxleft : x≤-4 := by dsimp [x]; omega
    have hprefix : T1 x=P.tape x := by
      change (frameAt P.tape 1
        firstCyclePrefix22Inside firstCyclePrefix22End).tape x=P.tape x
      rw [frameAt_tape]
      have hnot : firstCyclePrefix22Inside (x-1)=false := by
        simp [firstCyclePrefix22Inside]
        dsimp [x]
        omega
      simp [hnot]
    have htail := p2PostludeFrame_left_tail_local m n tail hn j
    have htarget :
        sideBit (p2NextQ4TailResidualTail tail) j =
          sideBit tail j := by
      unfold p2NextQ4TailResidualTail
      rw [Agent6Q4Prefix.sideBit_append_right
        ([true,true,true] : List Bool) (tail.drop 3) j (by simp; omega)]
      have hdrop := sideBit_drop_local tail 3 (j-3)
      have hidx : 3+(j-3)=j := by omega
      simpa [hidx] using hdrop
    calc
      T2 x = T1 x := hsetup
      _ = P.tape x := hprefix
      _ = sideBit tail j := htail
      _ = sideBit (p2NextQ4TailResidualTail tail) j := htarget.symm

/-- In the authentic root family the next residual is exactly
111111 ++ tail0.drop 6.  It does not begin with the P2 postlude's 100
guard, so the same postlude cannot be reapplied immediately. -/
theorem p2NextQ4Tail_authenticResidualTail
    (tail0 : List Bool) :
    p2NextQ4TailResidualTail
      ([true,false,false,true,true,true] ++ tail0.drop 6) =
    [true,true,true,true,true,true] ++ tail0.drop 6 := by
  simp [p2NextQ4TailResidualTail]

end BB6Coverage.Agent42P2NextQ4TailLeftResidual
