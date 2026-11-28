import Q0151B2AbstractActions
import Q0151ParamSaturation

set_option maxHeartbeats 0

/-!
Complete all-parameter B2/second-length-4k+4 finite-step coverage. The
source macro writes 1110 (10)^(2k+1) 11 and consumes the initial
physical run lengths 2 and 4k+4. The executable finite interpreter uses
j=1 at k=0 and j=2 at k>0. Exact parametric idempotence of the two-mode
segment summary proves their successors equal for EVERY k (no bounded
simulation or induction on observed concrete tapes).
-/

namespace BB6.Agent5Q0151B2EvenActionSound
open BB6.Agent5Q0151B2AbstractActions
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151ParamSaturation

theorem b2_even_action (s : SegmentSummary)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP)
    (n : Nat) (rest : List Nat)
    (h : rightType (rightSig (1::(4*n+3)::rest)) ≠ 0) :
    Action.stay (mkControl true (rightSig rest)
      (segAppend s
        ([true,true,true,false] ++ altWord (2*n+1) ++ [true,true]))) ∈
      delta (mkControl true (rightSig (1::(4*n+3)::rest)) s) := by
  cases n with
  | zero =>
      simpa using (second_four_action s rest h)
  | succ k =>
      have hh := second_eight_action s (k+1) (by omega)
        rest (by simpa using h)
      have hsat := two_zero_repair_positive s (k+2) (by omega)
        [true,true] hN hP
      have hlen : 2*(k+2)-1 = 2*(k+1)+1 := by omega
      rw [hlen] at hsat
      have hsat2 := two_zero_repair_positive s 2 (by decide)
        [true,true] hN hP
      have he :
          segAppend s ([true,true,true,false] ++
            altWord (2*(k+1)+1) ++ [true,true]) =
          segAppend s ([true,true,true,false] ++
            altWord 3 ++ [true,true]) := by
        calc
          _ = segAppend s ([true,true,true,false] ++
                altWord 1 ++ [true,true]) := hsat
          _ = segAppend s ([true,true,true,false] ++
                altWord 3 ++ [true,true]) := by
              simpa using hsat2.symm
      rw [he]
      exact hh

#print axioms b2_even_action
end BB6.Agent5Q0151B2EvenActionSound
