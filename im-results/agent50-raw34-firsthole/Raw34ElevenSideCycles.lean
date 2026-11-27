import SideCycle
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34Eleven

open BB6Coverage BB6Coverage.Agent50SideCycle

/-!
The original canonical Raw34 parent has the four defined nonhalting slots
A0=1RB, B0=1RC, C0=0RD, D0=1LC. Its first undefined query is D1 at
ordinary time 5. Eleven literal D1 branches admit a six-step-or-shorter
oriented right-half-line recurrence, for *every* total completion.

The witness table is data, not an oracle: all checks reduce in Lean,
and the generic finite-side-cycle soundness theorem proves nonhalting.
-/

def parent : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 2⟩)
  | _, _ => none

def child (mv : Move) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 2⟩)
  | 3, true => some (some mv)
  | _, _ => none

structure Witness where
  move : Move
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
  deriving DecidableEq

def witnesses : List Witness :=
  [ ⟨⟨false,false,0⟩, 0,6,true,0⟩  -- 0LA
  , ⟨⟨false,false,1⟩, 1,5,true,1⟩  -- 0LB
  , ⟨⟨false,false,2⟩, 2,4,true,2⟩  -- 0LC
  , ⟨⟨false,true,0⟩, 0,6,true,0⟩   -- 0RA
  , ⟨⟨false,true,1⟩, 1,5,true,1⟩   -- 0RB
  , ⟨⟨false,true,2⟩, 2,4,true,2⟩   -- 0RC
  , ⟨⟨false,true,3⟩, 3,3,true,2⟩   -- 0RD
  , ⟨⟨true,false,2⟩, 4,2,true,2⟩   -- 1LC
  , ⟨⟨true,true,0⟩, 0,6,true,0⟩    -- 1RA
  , ⟨⟨true,true,1⟩, 1,5,true,1⟩    -- 1RB
  , ⟨⟨true,true,2⟩, 2,4,true,2⟩ ]  -- 1RC

def check (w : Witness) : Bool :=
  decide (0 < w.period) &&
  fastSideCycleCheck (child w.move) w.entry w.period w.right w.boundary

theorem eleven_count : witnesses.length = 11 := by decide

theorem eleven_distinct : (witnesses.map (·.move)).Nodup := by decide

/-- Evaluates all eleven authentic blank-start recurrences in Lean. -/
theorem all_checked : witnesses.all check = true := by decide

/-- Every arbitrary full six-state completion extending any listed child
    has an infinite run on the blank tape, not merely a long simulation. -/
theorem all_never (w : Witness) (hw : w ∈ witnesses) :
    ∀ m : Machine, compatible (child w.move) m → NeverHalts m := by
  have h : check w = true :=
    List.all_eq_true.mp all_checked w hw
  have hparts :
      decide (0 < w.period) = true ∧
        fastSideCycleCheck (child w.move) w.entry w.period
          w.right w.boundary = true := by
    simpa [check, Bool.and_eq_true] using h
  exact fastSideCycleCheck_sound (child w.move) w.entry w.period
      w.right w.boundary (of_decide_eq_true hparts.1) hparts.2

#print axioms eleven_count
#print axioms eleven_distinct
#print axioms all_checked
#print axioms all_never
end BB6.Agent50Raw34Eleven
