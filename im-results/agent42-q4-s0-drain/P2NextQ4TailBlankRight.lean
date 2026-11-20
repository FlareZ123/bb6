import P2S0ToNextQ4Tail
import Lean.Elab.Tactic.Omega

/-!
# Full blank right ray at the next P2 q4Tail input

The existing P2 prefix theorem checks only the five local zero cells
needed by the first-cycle macro.  Reapplying the generic q4Tail-to-S0
adapter requires an infinite blank right ray.  This module proves that
ray directly from the unchanged S0 right encoder.

This is a source-level lemma; it has not been locally compiled in the
current invocation because the shell/Python tool boundary returned
ClientError before execution.  It is not a halting or BB(6) theorem.
-/

namespace BB6Coverage.Agent42P2NextQ4TailBlankRight

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

private theorem sideBit_false_ge_length_local
    (xs : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons b xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          simp only [sideBit]
          apply ih
          simp at hi
          omega

/-- The P2 postlude is a new unary run followed by the unchanged
right-facing stream of its drained S0 input. -/
private theorem p2PostludeFrame_right_cell_local
    (m n : Nat) (tail : List Bool) (hn : 2 ≤ n)
    (x : Int) (hx : 5 ≤ x) :
    (p2PostludeFrame m n tail).tape x =
      if x ≤ (m+2+3*n:Int)+1 then true
      else sideBit (s0RightFacing (2^(n-1)-1))
        (Int.toNat (x-(m+2+3*n:Int)-1)) := by
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
  have hframe :
      (p2PostludeFrame m n tail).tape x = U x := by
    change (q4FrameAt U 3 q4S0Final4Inside q4S0Final4End).tape x = U x
    rw [q4FrameAt_tape]
    have hnot : q4S0Final4Inside (x-3)=false := by
      simp [q4S0Final4Inside]
      omega
    simp [hnot]
  have hsweep := s0LeftSweep_shift K T H hk x
  have hprofile : U x = if x≤H+1 then true else T x := by
    rw [hsweep,hcenter]
    have hneq : x≠4 := by omega
    simp [hneq,hx]
  have hbase :
      (p2PostludeFrame m n tail).tape x =
        if x≤H+1 then true else T x := by
    rw [hframe,hprofile]
  by_cases hmid : x≤H+1
  · simpa [H,hmid] using hbase
  · have hnonneg : 0≤x-H-1 := by omega
    have hidx : (Int.toNat (x-H-1):Int)=x-H-1 :=
      Int.toNat_of_nonneg hnonneg
    have hcell := s0Config_right_cell ell a 0 (2^a-1) H
      (Int.toNat (x-H-1))
    have hcoord : H+1+(Int.toNat (x-H-1):Int)=x := by omega
    rw [hcoord] at hcell
    rw [hidx] at hcell
    simpa [H,hmid,T,a] using hbase.trans hcell

/-- The tape just before the next d0 sweep in the P2 recurrence. -/
def p2NextQ4TailInputTape (m n : Nat) (tail : List Bool) : Int → Bool :=
  let H : Int := (m+2+3*n)
  let P := p2PostludeFrame m n tail
  let T1 := (frameAt P.tape 1
    firstCyclePrefix22Inside firstCyclePrefix22End).tape
  afterFirstCycleTwoZero T1 (H+5)

/-- Head of the next q4Tail sweep, after the two-zero setup. -/
def p2NextQ4TailInputHead (m n : Nat) : Int :=
  (m+2+3*n:Int)+7

/-- The entire right ray required by q4Tail_frame_eq_s0Config is blank
at the next P2 q4Tail input.  The first cell on that ray is
H+12+3*2^(n-1), whose index in the old S0 right stream is
11+3*2^(n-1), five cells beyond its exact length 6+3*2^(n-1).
The prefix22 frame and two-zero setup lie strictly to the left. -/
theorem p2NextQ4Tail_blankRightRay
    (m n : Nat) (tail : List Bool) (hn : 2 ≤ n) (i : Nat) :
    p2NextQ4TailInputTape m n tail
      (p2NextQ4TailInputHead m n +
        3*(2^(n-1):Int)+5+(i:Int)) = false := by
  let a : Nat := n-1
  let H : Int := (m+2+3*n)
  let nNext : Nat := 2^a
  let P := p2PostludeFrame m n tail
  let T1 := (frameAt P.tape 1
    firstCyclePrefix22Inside firstCyclePrefix22End).tape
  let h1 : Int := H+5
  let T2 := afterFirstCycleTwoZero T1 h1
  let h2 : Int := H+7
  have hT2 : p2NextQ4TailInputTape m n tail = T2 := by
    rfl
  have hhead : p2NextQ4TailInputHead m n = h2 := by
    rfl
  rw [hT2,hhead]
  let x : Int := h2+3*(nNext:Int)+5+(i:Int)
  have hx : H+12+3*(nNext:Int)+(i:Int)=x := by
    dsimp [x,h2]
    omega
  have hx5 : 5≤x := by
    rw [← hx]
    dsimp [H]
    omega
  have hpost := p2PostludeFrame_right_cell_local m n tail hn x hx5
  have hmid : ¬ x≤H+1 := by
    rw [← hx]
    dsimp [H]
    omega
  have hpost' :
      P.tape x =
        sideBit (s0RightFacing (2^a-1))
          (Int.toNat (x-H-1)) := by
    simpa [hmid] using hpost
  have hprefix : T1 x=P.tape x := by
    change (frameAt P.tape 1
      firstCyclePrefix22Inside firstCyclePrefix22End).tape x = P.tape x
    rw [frameAt_tape]
    have hnot : firstCyclePrefix22Inside (x-1)=false := by
      simp [firstCyclePrefix22Inside]
      omega
    simp [hnot]
  have hsetup : T2 x=T1 x := by
    have hne0 : x≠h1 := by rw [← hx]; dsimp [h1,H]; omega
    have hne1 : x≠h1+1 := by rw [← hx]; dsimp [h1,H]; omega
    simp [T2,afterFirstCycleTwoZero,hne0,hne1]
  have hnonneg : 0≤x-H-1 := by
    rw [← hx]
    dsimp [H]
    omega
  have hidxInt :
      (Int.toNat (x-H-1):Int)=11+3*(nNext:Int)+(i:Int) := by
    rw [Int.toNat_of_nonneg hnonneg]
    rw [← hx]
    dsimp [x,h2]
    omega
  have hidx : Int.toNat (x-H-1)=11+3*nNext+i := by
    omega
  have hcoord : H+1+(Int.toNat (x-H-1):Int)=x := by
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  have hcell := s0Config_right_cell
    (p2ResidualLeft m tail) a 0 (2^a-1) H
    (Int.toNat (x-H-1))
  rw [hcoord] at hcell
  rw [hidx] at hcell
  have hlen : (s0RightFacing (2^a-1)).length=6+3*nNext := by
    simp [s0RightFacing,d1pow_length]
    have hp : 0<2^a := Nat.pow_pos (by decide)
    dsimp [nNext]
    omega
  have hbit :
      sideBit (s0RightFacing (2^a-1)) (11+3*nNext+i)=false := by
    apply sideBit_false_ge_length_local
    rw [hlen]
    omega
  calc
    T2 x = T1 x := hsetup
    _ = P.tape x := hprefix
    _ = sideBit (s0RightFacing (2^a-1))
          (Int.toNat (x-H-1)) := hpost'
    _ = sideBit (s0RightFacing (2^a-1))
          (11+3*nNext+i) := by rw [hidx]
    _ = false := hbit

#print axioms p2NextQ4Tail_blankRightRay

end BB6Coverage.Agent42P2NextQ4TailBlankRight
