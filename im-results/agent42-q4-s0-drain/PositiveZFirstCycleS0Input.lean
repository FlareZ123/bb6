import PositiveZFirstCycleBridges
import CountedSuffixOutput
import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Canonical S0 interface for the positive-z first-cycle Q macro

This module turns the explicit post-drain S0 configuration into the
hypotheses of Agent 48's `firstCycleQ_from_S0Input`.  The only residual
left-context assumption is an exact finite prefix:
  1^(3*z+7) ++ 0010 ++ arbitrary-tail.

The proof is entirely in the original S0 encoder and the generic
counted-sweep/Q bridge.  It does not assume the still-open P(z) prefix
theorem that must establish this residual-context shape.
-/

namespace BB6Coverage.Agent42PositiveZFirstCycleS0Input

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48PositiveZFirstCycle

/-- Residual left context required after the all-ones S0 drain. -/
def firstCycleResidualLeft (z : Nat) (tail : List Bool) : List Bool :=
  List.replicate (3*z+7) true ++ [false,true,false,false] ++ tail

/-- The exact S0 input before the counted drain in the first positive-z
q4 cycle.  Its low counter is all ones, so the subsequent drain changes
the left-facing d0^a block to d1^a. -/
def firstCycleS0DrainOutput (z : Nat) (tail : List Bool) : Config :=
  s0Config (firstCycleResidualLeft z tail) (2^z-1) 0
    (2^(2^z-1)-1) (3*2^z+3*z+7)

/-- Every bit in a finite repeated-one word is one. -/
private theorem sideBit_replicate_true (n i : Nat) (hi : i<n) :
    sideBit (List.replicate n true) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => rw [List.replicate_succ]; rfl
      | succ i =>
          have hi' : i<n := by omega
          rw [List.replicate_succ]
          exact ih i hi'

/-- The four-cell suffix after the leading one-run is exactly 0,1,0,0
in head-facing order. -/
private theorem firstCycleResidualLeft_boundary (z : Nat) (tail : List Bool) :
    sideBit (firstCycleResidualLeft z tail) (3*z+7) = false ∧
    sideBit (firstCycleResidualLeft z tail) (3*z+8) = true ∧
    sideBit (firstCycleResidualLeft z tail) (3*z+9) = false ∧
    sideBit (firstCycleResidualLeft z tail) (3*z+10) = false := by
  let m := 3*z+7
  have hbit (j : Nat) (hj : j<4) :
      sideBit (firstCycleResidualLeft z tail) (m+j) =
        sideBit [false,true,false,false] j := by
    unfold firstCycleResidualLeft
    rw [List.append_assoc]
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (List.replicate m true) ([false,true,false,false] ++ tail) (m+j)
      (by simp [List.length_replicate])]
    have hidx : m+j-(List.replicate m true).length = j := by
      simp [List.length_replicate]
    rw [hidx, sideBit_append]
    simp [hj, sideBit]
  refine ⟨?_,?_,?_,?_⟩
  · simpa [m,sideBit] using hbit 0 (by omega)
  · simpa [m,sideBit] using hbit 1 (by omega)
  · simpa [m,sideBit] using hbit 2 (by omega)
  · simpa [m,sideBit] using hbit 3 (by omega)

/-- The drained S0 left-facing stream begins with d1^a followed by the
residual left context. -/
private theorem firstCycleS0DrainOutput_leftFacing (z : Nat) (tail : List Bool) :
    s0LeftFacing (firstCycleResidualLeft z tail) (2^z-1) 0 =
      d1pow (2^z-1) ++ firstCycleResidualLeft z tail := by
  simp [s0LeftFacing, binDec_zero]

/-- The post-drain tape has the contiguous left-one run required by Q(z):
the d1^a counter followed by the residual 1^(3z+7) prefix. -/
theorem firstCycleS0DrainOutput_leftOnes (z : Nat) (tail : List Bool) :
    leftOnes (firstCycleS0DrainOutput z tail).tape
      (3*2^z+3*z+7)
      (3*(2^z-1)+3*z+7) := by
  let a := 2^z-1
  let m := 3*z+7
  let h : Int := (3*2^z+3*z+7)
  let l := firstCycleResidualLeft z tail
  let T := (firstCycleS0DrainOutput z tail).tape
  have hleft :
      s0LeftFacing l a 0 = d1pow a ++ l := by
    simpa [a,l] using firstCycleS0DrainOutput_leftFacing z tail
  intro i hi
  have hcell := s0Config_left_cell l a 0 (2^a-1) h i
  rw [hleft] at hcell
  have hside : sideBit (d1pow a ++ l) i = true := by
    by_cases hlt : i < 3*a
    · rw [sideBit_append, d1pow_length]
      simp [hlt, Agent6Q4Prefix.sideBit_d1pow_true a i hlt]
    · have hj : i-3*a < m := by omega
      rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
        (d1pow a) l i (by rw [d1pow_length]; omega)]
      rw [d1pow_length]
      have hprefix : sideBit l (i-3*a) = true := by
        change sideBit
          (List.replicate m true ++ [false,true,false,false] ++ tail)
          (i-3*a) = true
        rw [List.append_assoc]
        rw [sideBit_append]
        have hltm : i-3*a < (List.replicate m true).length := by
          simpa [List.length_replicate] using hj
        simp [hj, List.length_replicate,
          sideBit_replicate_true m (i-3*a) hj]
      exact hprefix
  calc
    (firstCycleS0DrainOutput z tail).tape
        ((3*2^z+3*z+7)-(i:Int)) =
      sideBit (d1pow a ++ l) i := by
        simpa [T, firstCycleS0DrainOutput, a, l, h] using hcell
    _ = true := hside

/-- The first cell to the right of the S0 head is blank, independently
of the drained counter value. -/
theorem firstCycleS0DrainOutput_rightZero (z : Nat) (tail : List Bool) :
    (firstCycleS0DrainOutput z tail).tape
      ((3*2^z+3*z+7:Int)+1) = false := by
  let a := 2^z-1
  let h : Int := (3*2^z+3*z+7)
  have hcell := s0Config_right_cell
    (firstCycleResidualLeft z tail) a 0 (2^a-1) h 0
  simpa [firstCycleS0DrainOutput, firstCycleResidualLeft, a, h,
    s0RightFacing, sideBit] using hcell

/-- Convert the four bits of the residual word into the absolute-cell
guard used by the Q(z) postlude. -/
private theorem firstCycleS0DrainOutput_cell (z : Nat) (tail : List Bool)
    (x : Nat) (hx : x≤3) :
    (firstCycleS0DrainOutput z tail).tape (x:Int) =
      sideBit (firstCycleResidualLeft z tail) (3*z+10-x) := by
  let a := 2^z-1
  let m := 3*z+7
  let h : Int := (3*2^z+3*z+7)
  let l := firstCycleResidualLeft z tail
  let T := (firstCycleS0DrainOutput z tail).tape
  have hpow : 0 < 2^z := Nat.pow_pos (by decide)
  have hnum : 3*a+m+3 = 3*2^z+3*z+7 := by
    dsimp [a,m]
    omega
  have hcoord :
      h-((3*a+m+3-x:Nat):Int) = (x:Int) := by
    rw [Int.ofNat_sub (by omega : x ≤ 3*a+m+3)]
    have hc : ((3*a+m+3:Nat):Int) = h := by
      rw [hnum]
      dsimp [h]
    rw [hc]
    omega
  have hleft :
      s0LeftFacing l a 0 = d1pow a ++ l := by
    simpa [a,l] using firstCycleS0DrainOutput_leftFacing z tail
  have hcell := s0Config_left_cell l a 0 (2^a-1) h (3*a+m+3-x)
  rw [hcoord] at hcell
  rw [hleft] at hcell
  have hside :
      sideBit (d1pow a ++ l) (3*a+m+3-x) =
        sideBit l (m+3-x) := by
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (d1pow a) l (3*a+m+3-x)
      (by rw [d1pow_length]; omega)]
    rw [d1pow_length]
    rw [show 3*a+m+3-x-3*a=m+3-x by dsimp [m]; omega]
  calc
    T (x:Int) =
        sideBit (d1pow a ++ l) (3*a+m+3-x) := by
          simpa [T, firstCycleS0DrainOutput, a, l, h] using hcell
    _ = sideBit l (m+3-x) := hside
    _ = sideBit (firstCycleResidualLeft z tail) (3*z+10-x) := by
          rfl

/-- The absolute cells 0..3 are 0,0,1,0, exactly the final-four
guard required by Agent 48's Q(z) bridge. -/
theorem firstCycleS0DrainOutput_localCells (z : Nat) (tail : List Bool) :
    (firstCycleS0DrainOutput z tail).tape 0 = false ∧
    (firstCycleS0DrainOutput z tail).tape 1 = false ∧
    (firstCycleS0DrainOutput z tail).tape 2 = true ∧
    (firstCycleS0DrainOutput z tail).tape 3 = false := by
  have hbits := firstCycleResidualLeft_boundary z tail
  refine ⟨?_,?_,?_,?_⟩
  · have h := firstCycleS0DrainOutput_cell z tail 0 (by omega)
    simpa [hbits.2.2.2] using h
  · have h := firstCycleS0DrainOutput_cell z tail 1 (by omega)
    simpa [hbits.2.2.1] using h
  · have h := firstCycleS0DrainOutput_cell z tail 2 (by omega)
    simpa [hbits.2.1] using h
  · have h := firstCycleS0DrainOutput_cell z tail 3 (by omega)
    simpa [hbits.1] using h

/-- The Q(z) macro now applies directly to the canonical drained S0
configuration, under only the explicit residual-left-prefix condition. -/
theorem firstCycleQ_from_drainedS0 (z : Nat) (tail : List Bool) :
    run tm2 (9*2^z+9*z+16) (firstCycleS0DrainOutput z tail) =
      some (frameAt
        (sweptLeft (3*(2^z-1)+3*z+7)
          (firstCycleS0DrainOutput z tail).tape
          (3*2^z+3*z+7))
        3 firstCyclePostludeInside firstCyclePostludeEnd) := by
  let T := (firstCycleS0DrainOutput z tail).tape
  let h : Int := (3*2^z+3*z+7)
  have hleft := firstCycleS0DrainOutput_leftOnes z tail
  have hright := firstCycleS0DrainOutput_rightZero z tail
  have hlocal := firstCycleS0DrainOutput_localCells z tail
  change run tm2 (9*2^z+9*z+16) ⟨3,h,T⟩ =
    some (frameAt
      (sweptLeft (3*(2^z-1)+3*z+7) T h)
      3 firstCyclePostludeInside firstCyclePostludeEnd)
  exact firstCycleQ_from_S0Input z T h rfl hleft hright
    hlocal.1 hlocal.2.1 hlocal.2.2.1 hlocal.2.2.2

#print axioms firstCycleS0DrainOutput_leftOnes
#print axioms firstCycleS0DrainOutput_rightZero
#print axioms firstCycleS0DrainOutput_localCells
#print axioms firstCycleQ_from_drainedS0

end BB6Coverage.Agent42PositiveZFirstCycleS0Input
