import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56.LE17557Base
open BB6Coverage BB6Coverage.Agent31Pump

/-- Sole residual of the source-accepted Raw56 E0=1LF 1307-to-1 theorem.
    Only F1 is undefined. -/
def p : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true,  true,  1⟩)
  | 0, true  => some (some ⟨true,  false, 0⟩)
  | 1, false => some (some ⟨true,  true,  2⟩)
  | 1, true  => some (some ⟨true,  true,  1⟩)
  | 2, false => some (some ⟨false, true,  3⟩)
  | 2, true  => some (some ⟨false, true,  2⟩)
  | 3, false => some (some ⟨true,  false, 3⟩)
  | 3, true  => some (some ⟨true,  false, 4⟩)
  | 4, false => some (some ⟨true,  false, 5⟩)
  | 4, true  => some (some ⟨false, false, 4⟩)
  | 5, false => some (some ⟨false, false, 0⟩)
  | 5, true  => none
  | _, _ => none

def ones (n : Nat) : List Bool := rep [true] n

/-- Translation-invariant checkpoint C_n.  The head is in state A scanning
    blank, with blank tape strictly to its left. -/
def checkpoint (n : Nat) : Z0 :=
  ⟨0, [],
    ones (2^n - 2) ++ [false] ++
    ones (2^(n+1) - 3) ++ [false] ++
    ones (2^(n+1) - 1)⟩

def clock (n : Nat) : Nat :=
  4 * 4^n + 8 * 3^(n-1) - 7 * 2^n - 1

/-- Exact finite entry from blank to C_2. -/
theorem entryC2 :
    run0 p 59 ⟨0, [], []⟩ = some (checkpoint 2) := by
  decide

/-- Exact finite base epoch C_2 -> C_3.  The renormalization proof under
    development is intended to lift this one epoch to every n. -/
theorem baseEpoch :
    run0 p 212 (checkpoint 2) = some (checkpoint 3) := by
  decide

theorem clock2 : clock 2 = 59 := by decide
theorem clock3 : clock 3 = 271 := by decide
theorem baseCost : clock 3 - clock 2 = 212 := by decide

#print axioms entryC2
#print axioms baseEpoch
end BB6.Agent1Raw56.LE17557Base
