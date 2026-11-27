import MixedCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
namespace F197.MarkerCarry
open JCarry MixedCarry

def vv : Tape → Tape := pre [true,true,false,false,false]
def inc2 (r : Tape) := inc (inc r)
def rmark (r : Tape) := vv (a (tau (inc2 r)))
def powP : Nat → Tape → Tape
  | 0,l => l
  | n+1,l => p (powP n l)
def powS : Nat → Tape → Tape
  | 0,r => r
  | n+1,r => s (powS n r)
def jprefix (v : Bool) (l : Tape) := j (t (p (a (h v l))))

theorem ppj (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 141 (b (p (p (j l))) r) = some (b (t l) (rmark r)) := by
  rw [← decompose_bit l true hl, ← decompose_bit r true hr]
  rfl

theorem marker_base (v : Bool) (l : Tape) (hl : l 0 = true) :
    run (50 + 4 * bit v) (b (j l) (x (dcode v (rmark e)))) =
    some (b (jprefix v l) e) := by
  cases v <;> rw [← decompose_bit l true hl] <;> rfl

theorem marker_step (v : Bool) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (55 + 4 * bit v) (b (j l) (x (dcode v (rmark (u r))))) =
    some (b (j (jprefix v l)) (x r)) := by
  cases v <;> rw [← decompose_bit l true hl, ← decompose_bit r true hr] <;> rfl

theorem powP_first (n : Nat) (l : Tape) (hl : l 0 = true) : powP n l 0 = true := by
  cases n with | zero => exact hl | succ n => rfl

theorem powS_first (n : Nat) (r : Tape) (hr : r 0 = true) : powS n r 0 = true := by
  cases n with | zero => exact hr | succ n => rfl

#print axioms ppj
#print axioms marker_base
#print axioms marker_step
end F197.MarkerCarry
