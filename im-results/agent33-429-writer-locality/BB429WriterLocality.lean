import BB429PhysicalFrontier
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

namespace BB429WriterLocality

open BB6Coverage BB429PhysicalFrontier

/-- Prepared D/0 with exactly the eight left bits of the genuine blank
    D/0 writer at primitive time 276: 0xFE, nearest bit first. -/
def dSeed : Config :=
  { state := ⟨3, by decide⟩
    head := 0
    tape := fun x => x = -2 || x = -3 || x = -4 || x = -5 ||
                     x = -6 || x = -7 || x = -8 }

/-- Prepared F/1 with exactly the eight left bits of the genuine blank
    F/1 writer at primitive time 283: 0x57, nearest bit first. -/
def fSeed : Config :=
  { state := ⟨5, by decide⟩
    head := 0
    tape := fun x => x = 0 || x = -1 || x = -2 || x = -3 ||
                     x = -5 || x = -7 }

def c01Observation (c : Config) : Nat × Int × Bool × Bool :=
  (c.state.val, c.head, c.tape c.head, c.tape (c.head+1))

/-- Exact source-physical finite synthetic fatal C/01, 27 steps after D/0. -/
theorem d_prepared_reaches_fatal :
    (run target429 27 dSeed).map c01Observation =
      some (2, -1, false, true) := by decide

/-- Exact source-physical finite synthetic fatal C/01, 59 steps after F/1. -/
theorem f_prepared_reaches_fatal :
    (run target429 59 fSeed).map c01Observation =
      some (2, -1, false, true) := by decide

/-- The D synthetic prefix does not revisit its marked writer cell at 0
    after departure, so this is a one-sided last-writer excursion. -/
theorem d_prepared_one_sided :
    (List.range 28).all (fun j => decide
      (∃ c, run target429 j dSeed = some c ∧ c.head ≤ 0)) = true := by decide

/-- Likewise the F synthetic prefix stays strictly left of its writer
    boundary at 0 after the first instruction. -/
theorem f_prepared_one_sided :
    (List.range 60).all (fun j => decide
      (∃ c, run target429 j fSeed = some c ∧ c.head ≤ 0)) = true := by decide

/-- Read the nearest eight bits on the left of the physical head. -/
def leftEight (c : Config) : List Bool :=
  (List.range 8).map (fun j => c.tape (c.head - Int.ofNat (j+1)))

def writerObservation (c : Config) : Nat × Int × Bool × List Bool :=
  (c.state.val, c.head, c.tape c.head, leftEight c)

/-- Actual blank-origin D/0 at time 276, including the root's left prefix. -/
theorem genuine_d_writer_276 :
    (run target429 276 blank).map writerObservation =
      some (3, 16, false, [false,true,true,true,true,true,true,true]) := by decide

/-- Actual blank-origin F/1 at time 283, including the root's left prefix. -/
theorem genuine_f_writer_283 :
    (run target429 283 blank).map writerObservation =
      some (5, 9, true, [true,true,true,false,true,false,true,false]) := by decide

#print axioms d_prepared_reaches_fatal
#print axioms f_prepared_reaches_fatal
#print axioms d_prepared_one_sided
#print axioms f_prepared_one_sided
#print axioms genuine_d_writer_276
#print axioms genuine_f_writer_283

end BB429WriterLocality
