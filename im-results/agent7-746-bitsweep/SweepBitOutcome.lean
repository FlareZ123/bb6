import FastForward
import SweepBitLengthBridge

namespace CascadeFastReturn

/-- Source-equivalent first-reset successor using a binary-length sweep guard. -/
def bitOutcome (h : Nat) : Option Nat :=
  let k := CascadeBitSweep.firstFailIndex h
  if h+k+4=4*2^k then none
  else if (h+k)%2=0 then some (4*2^k+(h+k)/2)
  else
    let q := 4*2^k+(h+k)/2+3
    let t := (stripTwos q).1
    let d := (stripTwos q).2
    some ((3^(t+1)*d-5)/2)

theorem bitOutcome_eq_fastOutcome (h : Nat) :
    bitOutcome h = fastOutcome h := by
  simp [bitOutcome, fastOutcome, firstFailedK_eq_bit]

theorem bitOutcome_sound (h : Nat) :
    CascadeResetInverse.Outcome (h,0) (bitOutcome h) := by
  rw [bitOutcome_eq_fastOutcome]
  exact fastOutcome_sound h

/-- Any finite root trajectory is definitionally transportable to the accelerated evaluator. -/
def runBit (start : Nat) : Nat → Option Nat
  | 0 => some start
  | n+1 => (runBit start n).bind bitOutcome

theorem runBit_eq_runFast (start steps : Nat) :
    runBit start steps = runFast start steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [runBit, runFast, ih]
    cases h : runFast start steps with
    | none => rfl
    | some u => simp [bitOutcome_eq_fastOutcome]

#print axioms bitOutcome_eq_fastOutcome
#print axioms bitOutcome_sound
#print axioms runBit_eq_runFast

end CascadeFastReturn
