import W4ScanE
import W4JuncMax
import W4HeadPrefix
import PositiveRegularHeadMax
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2BoundaryHeadMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion BB429W4ScanE
open BB429W4HeadMax BB429W4JuncMax BB429W4HeadPrefix
open BB429PositiveRegularHeadMax

/-- The B/1 to A/1 step advances one position. -/
theorem b1_w2_to_boundary_max (tail : List Bool) :
    runWithMax 1 (z 1 tail true [true,false,true]) =
      some (z 0 (true::tail) true [false,true],1,1) := by rfl

/-- Exact primitive-step head record 2v+3 at the A/1 boundary after
    2v+27 steps of an arbitrary right-two Junc(0,v,2). -/
theorem junc0_w2_to_boundary_max (v : Nat) :
    runWithMax (2*v+27) (junc 0 v 2) =
      some (z 0 (true::(pairs01 (v+3) ++ ones 5)) true [false,true],
        ((2*v+3 : Nat) : Int), ((2*v+3 : Nat) : Int)) := by
  have hprep := junc0_prep20_max v 2
  have hshift := shift_B01_max (v+2) (ones 5) [true,false,true]
  have htail := b1_w2_to_boundary_max (pairs01 (v+3) ++ ones 5)
  have hinput : z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ ones 2 ++ [false,true])) =
      z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ (true::[true,false,true]))) := by
    simp [ones,List.append_assoc]
  have htime : 2*v+27 = 20 + (2*((v+2)+1)+1) := by omega
  rw [htime,runWithMax_add,hprep]
  simp only [Option.bind_some]
  rw [hinput,runWithMax_add,hshift]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- Each nineteen-step A/1 fringe reaches S_E with maximum +5 and
    signed displacement -3, for an unbounded alternating left prefix. -/
theorem boundary_w2_to_ScanE_max (v : Nat) :
    runWithMax 19
        (z 0 (true::(pairs01 (v+5) ++ ones 5)) true [false,true]) =
      some (sourceScanE (v+4) (sourceSuffix 0),-3,5) := by rfl

/-- The fixed twelve-step finishC to A fringe has sharp maximum +4. -/
theorem finishC_to_A_max (left suffix : List Bool) :
    runWithMax 12 (z 2 left true (ones 6 ++ suffix)) =
      some (z 0 left true (true :: (pairs01 2 ++ (true :: suffix))),0,4) := by rfl

/-- The entire finishC phase never exceeds its entry head by more than
    four cells. Its net movement and canonical Junc endpoint are checked
    against the independent original-source signed interpreter. -/
theorem finishC_ScanE_max (u p k : Nat) :
    runWithMax (12+2*p) (finishCStart u p k) =
      some (junc u (p+2) (2*k+1), -((2*p : Nat) : Int), 4) := by
  let left : List Bool := pairs01 u ++ ones 5
  let suffix : List Bool := pairs01 2 ++ (true :: (ones (2*k) ++ [false,true]))
  have hfirst : runWithMax 12 (finishCStart u p k) =
      some (z 0 (true::(ones (2*p) ++ left)) true (true::suffix),0,4) := by
    simpa [finishCStart,left,suffix,ones,pairs01,List.append_assoc] using
      finishC_to_A_max (true::(ones (2*p) ++ left))
        (ones (2*k) ++ [false,true])
  have hsecond := shift_A11_max p left suffix
  have hcomp : runWithMax (12+2*p) (finishCStart u p k) =
      some (z 0 (true::left) true (true::(pairs01 p ++ suffix)),
        -((2*p : Nat) : Int), 4) := by
    rw [runWithMax_add,hfirst]
    simp only [Option.bind_some]
    rw [hsecond]
    simp [Int.max_def]
  have hp := runWithMax_toDelta (12+2*p) (finishCStart u p k)
  rw [hcomp,finishC_ScanE_delta] at hp
  simp only [Option.map_some, Option.some.injEq,Prod.mk.injEq] at hp
  rcases hp with ⟨hcfg,hd⟩
  rw [hcomp]
  simp only [Option.some.injEq,Prod.mk.injEq]
  constructor
  · exact hcfg
  · constructor <;> rfl

/-- The entire even partial sweep, from its A/1 fringe through S_E and
    finishC, remains within five cells of its initial A/1 boundary. -/
theorem even_boundary_to_junc2_max (k : Nat) :
  runWithMax (18*k+109)
    (z 0 (true::(pairs01 (2*k+5) ++ ones 5)) true [false,true]) =
  some (junc 2 (2*k+6) 1, -((4*k+11 : Nat) : Int),5) := by
  have h19 := boundary_w2_to_ScanE_max (2*k)
  have hE := sourceScanE_e1_max (2*k+4) (sourceSuffix 0)
  have hF := finishC_ScanE_max 2 (2*k+4) 0
  have hmid : z 2 (finalLeft (2*k+4)) true (sourceSuffix 0) =
      finishCStart 2 (2*k+4) 0 := by
    simpa only [show 2*(k+2)=2*k+4 by omega] using
      finalLeft_even_finishC_entry (k+2) 0
  have htime : 18*k+109 = 19+((crossTime (2*k+4)+1)+(12+2*(2*k+4))) := by
    rw [show 2*k+4=2*(k+2) by omega,crossTime_even]
    omega
  rw [htime,runWithMax_add,h19]
  simp only [Option.bind_some]
  rw [runWithMax_add,hE]
  simp only [Option.bind_some]
  have hparam : (2*k+4)+2=2*k+6 := by omega
  rw [hparam] at hF
  rw [hmid,hF]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- The corresponding odd partial sweep has the same five-cell
    all-prefix head barrier, with the exact odd Junc endpoint. -/
theorem odd_boundary_to_junc0_max (k : Nat) :
  runWithMax (18*k+85)
    (z 0 (true::(pairs01 (2*k+6) ++ ones 5)) true [false,true]) =
  some (junc 0 (2*k+7) 1, -((4*k+13 : Nat) : Int),5) := by
  have h19 := boundary_w2_to_ScanE_max (2*k+1)
  have hE := sourceScanE_e1_max (2*k+5) (sourceSuffix 0)
  have hF := finishC_ScanE_max 0 (2*k+5) 0
  have hmid : z 2 (finalLeft (2*k+5)) true (sourceSuffix 0) =
      finishCStart 0 (2*k+5) 0 := by
    simpa only [show 2*(k+2)+1=2*k+5 by omega] using
      finalLeft_odd_finishC_entry (k+2) 0
  have htime : 18*k+85 = 19+((crossTime (2*k+5)+1)+(12+2*(2*k+5))) := by
    rw [show 2*k+5=2*(k+2)+1 by omega,crossTime_odd]
    omega
  rw [htime,runWithMax_add,h19]
  simp only [Option.bind_some]
  rw [runWithMax_add,hE]
  simp only [Option.bind_some]
  have hparam : (2*k+5)+2=2*k+7 := by omega
  rw [hparam] at hF
  rw [hmid,hF]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

#print axioms junc0_w2_to_boundary_max
#print axioms boundary_w2_to_ScanE_max
#print axioms finishC_ScanE_max
#print axioms even_boundary_to_junc2_max
#print axioms odd_boundary_to_junc0_max

end BB429W2BoundaryHeadMax
