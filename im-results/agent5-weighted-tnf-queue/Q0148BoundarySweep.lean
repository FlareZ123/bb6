import Agent5PackedSweep

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent5Q0148BoundarySweep
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto
open BB6Coverage.Agent13PackedZipper BB6.Agent5PackedSweep

/-- Original q0-148 F1-open table, not a completed halting program. -/
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => none
  | _,_ => none

/-- The entire local machine calculation on a leftward alternating block.
    The finite checker forbids reading beyond the listed stack prefixes. -/
theorem leftOne :
    Auto.knownRun p 2 ⟨2,[false,true,false],[]⟩ =
      some ⟨2,[false],[true,false]⟩ := by decide +kernel

/-- Parametric left pass across n copies of 10, with arbitrary
    untouched (unbounded) left and right tape tails L and R. -/
theorem transparentLeft (n L R : Nat) :
    runP p (2*n)
      ⟨2,cat [false] (repCat [true,false] n L),cat [] R⟩ =
    some ⟨2,cat [false] L,cat [] (repCat [true,false] n R)⟩ :=
  sweepLP p 2 [false] [] [true,false] [true,false] 2 n L R leftOne

/-- The rightward six-step block, including the fixed zero-cell frame
    immediately to the right of the head. -/
theorem rightOne :
    Auto.knownRun p 6 ⟨0,[false],[false,true,false]⟩ =
      some ⟨0,[false,false,true],[false]⟩ := by decide +kernel

/-- Parametric right pass: copies of 10 to the right become copies of
    01 on the left, with the two fixed zero frame cells retained. -/
theorem transparentRight (n L R : Nat) :
    runP p (6*n)
      ⟨0,cat [false] L,cat [false] (repCat [true,false] n R)⟩ =
    some ⟨0,cat [false] (repCat [false,true] n L),cat [false] R⟩ :=
  sweepRP p 0 [false] [false] [true,false] [false,true] 6 n L R rightOne

#print axioms leftOne
#print axioms transparentLeft
#print axioms rightOne
#print axioms transparentRight
end BB6.Agent5Q0148BoundarySweep
