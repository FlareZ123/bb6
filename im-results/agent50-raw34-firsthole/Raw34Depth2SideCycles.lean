import Raw34ElevenSideCycles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34Depth2
open BB6Coverage BB6Coverage.Agent50SideCycle

/-!
Original-source universal nonhalting for 74 second-level Raw34 first-hole
cylinders. These are disjoint from the eleven accepted first-level cylinders.
Each certificate proves an infinite blank-start right/left half-line recurrence.
-/
structure Witness where
  first : Move
  slot : Slot
  second : Move
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
  deriving DecidableEq

def table (w : Witness) : PartialMachine :=
  BB6Coverage.refine
    (BB6.Agent50Raw34Eleven.child w.first) w.slot (some w.second)

def witnesses : List Witness := [
  ⟨⟨false,false,3⟩,(2,true),⟨false,false,2⟩,10,3,false,0⟩,
  ⟨⟨false,false,3⟩,(2,true),⟨false,false,3⟩,8,3,false,0⟩,
  ⟨⟨false,false,3⟩,(2,true),⟨false,true,2⟩,23,3,false,3⟩,
  ⟨⟨false,false,3⟩,(2,true),⟨false,true,3⟩,11,3,false,1⟩,
  ⟨⟨false,false,3⟩,(2,true),⟨true,false,2⟩,9,3,false,0⟩,
  ⟨⟨false,false,3⟩,(2,true),⟨true,false,3⟩,8,3,false,0⟩,
  ⟨⟨false,false,3⟩,(2,true),⟨true,true,2⟩,2,7,true,1⟩,
  ⟨⟨false,false,3⟩,(2,true),⟨true,true,3⟩,10,3,false,0⟩,
  ⟨⟨false,false,4⟩,(4,false),⟨false,true,0⟩,0,7,true,0⟩,
  ⟨⟨false,false,4⟩,(4,false),⟨false,true,1⟩,1,6,true,1⟩,
  ⟨⟨false,false,4⟩,(4,false),⟨false,true,2⟩,2,5,true,2⟩,
  ⟨⟨false,false,4⟩,(4,false),⟨false,true,3⟩,3,4,true,2⟩,
  ⟨⟨false,false,4⟩,(4,false),⟨false,true,4⟩,6,1,true,2⟩,
  ⟨⟨false,false,4⟩,(4,false),⟨true,true,0⟩,0,7,true,0⟩,
  ⟨⟨false,false,4⟩,(4,false),⟨true,true,1⟩,1,6,true,1⟩,
  ⟨⟨false,false,4⟩,(4,false),⟨true,true,2⟩,2,5,true,2⟩,
  ⟨⟨false,false,4⟩,(4,false),⟨true,true,4⟩,6,1,true,2⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨false,false,0⟩,0,7,true,0⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨false,false,1⟩,1,6,true,1⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨false,false,2⟩,2,5,true,2⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨false,false,3⟩,3,4,true,2⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨false,true,0⟩,0,7,true,0⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨false,true,1⟩,1,6,true,1⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨false,true,2⟩,2,5,true,2⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨false,true,3⟩,3,4,true,2⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨false,true,4⟩,6,1,true,4⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨true,false,2⟩,4,3,true,2⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨true,true,0⟩,0,7,true,0⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨true,true,1⟩,1,6,true,1⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨true,true,2⟩,2,5,true,2⟩,
  ⟨⟨false,true,4⟩,(4,false),⟨true,true,4⟩,6,1,true,4⟩,
  ⟨⟨true,false,0⟩,(1,true),⟨false,false,1⟩,8,9,false,2⟩,
  ⟨⟨true,false,0⟩,(1,true),⟨false,true,0⟩,0,8,true,0⟩,
  ⟨⟨true,false,0⟩,(1,true),⟨false,true,1⟩,1,7,true,1⟩,
  ⟨⟨true,false,0⟩,(1,true),⟨false,true,2⟩,2,6,true,2⟩,
  ⟨⟨true,false,0⟩,(1,true),⟨false,true,3⟩,3,5,true,2⟩,
  ⟨⟨true,false,0⟩,(1,true),⟨true,true,0⟩,0,8,true,0⟩,
  ⟨⟨true,false,0⟩,(1,true),⟨true,true,1⟩,1,7,true,1⟩,
  ⟨⟨true,false,0⟩,(1,true),⟨true,true,2⟩,2,6,true,2⟩,
  ⟨⟨true,false,1⟩,(2,true),⟨false,false,2⟩,9,7,false,1⟩,
  ⟨⟨true,false,1⟩,(2,true),⟨false,true,0⟩,0,8,true,0⟩,
  ⟨⟨true,false,1⟩,(2,true),⟨false,true,1⟩,1,7,true,1⟩,
  ⟨⟨true,false,1⟩,(2,true),⟨false,true,2⟩,2,6,true,2⟩,
  ⟨⟨true,false,1⟩,(2,true),⟨false,true,3⟩,3,5,true,2⟩,
  ⟨⟨true,false,1⟩,(2,true),⟨true,false,2⟩,9,5,false,1⟩,
  ⟨⟨true,false,1⟩,(2,true),⟨true,true,0⟩,0,8,true,0⟩,
  ⟨⟨true,false,1⟩,(2,true),⟨true,true,1⟩,1,7,true,1⟩,
  ⟨⟨true,false,1⟩,(2,true),⟨true,true,2⟩,2,6,true,2⟩,
  ⟨⟨true,false,3⟩,(2,true),⟨false,false,2⟩,10,3,false,0⟩,
  ⟨⟨true,false,3⟩,(2,true),⟨false,false,3⟩,8,3,false,0⟩,
  ⟨⟨true,false,3⟩,(2,true),⟨false,true,2⟩,31,3,false,7⟩,
  ⟨⟨true,false,3⟩,(2,true),⟨false,true,3⟩,11,3,false,1⟩,
  ⟨⟨true,false,3⟩,(2,true),⟨true,false,2⟩,9,3,false,0⟩,
  ⟨⟨true,false,3⟩,(2,true),⟨true,false,3⟩,8,3,false,0⟩,
  ⟨⟨true,false,3⟩,(2,true),⟨true,true,2⟩,2,8,true,1⟩,
  ⟨⟨true,false,3⟩,(2,true),⟨true,true,3⟩,10,3,false,0⟩,
  ⟨⟨true,false,4⟩,(4,false),⟨false,true,3⟩,5,2,true,2⟩,
  ⟨⟨true,true,3⟩,(2,true),⟨false,false,1⟩,4,5,true,2⟩,
  ⟨⟨true,true,3⟩,(2,true),⟨false,false,3⟩,10,5,false,1⟩,
  ⟨⟨true,true,3⟩,(2,true),⟨false,true,2⟩,2,7,true,2⟩,
  ⟨⟨true,true,3⟩,(2,true),⟨false,true,3⟩,5,3,true,3⟩,
  ⟨⟨true,true,3⟩,(2,true),⟨true,false,3⟩,12,5,true,2⟩,
  ⟨⟨true,true,3⟩,(2,true),⟨true,true,2⟩,2,7,true,2⟩,
  ⟨⟨true,true,3⟩,(2,true),⟨true,true,3⟩,5,3,true,3⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨false,false,3⟩,5,2,true,3⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨false,true,0⟩,0,7,true,0⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨false,true,1⟩,1,6,true,1⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨false,true,2⟩,2,5,true,2⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨false,true,3⟩,3,4,true,2⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨false,true,4⟩,6,1,true,4⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨true,true,0⟩,0,7,true,0⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨true,true,1⟩,1,6,true,1⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨true,true,2⟩,2,5,true,2⟩,
  ⟨⟨true,true,4⟩,(4,false),⟨true,true,4⟩,6,1,true,4⟩
]

def check (w : Witness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w) w.entry w.period w.right w.boundary

theorem witness_count : witnesses.length = 74 := by decide

theorem pairwise_key_distinct :
    (witnesses.map (fun w => (w.first,w.slot,w.second))).Nodup := by decide

theorem separate_from_first_level :
    witnesses.all (fun w =>
      !((BB6.Agent50Raw34Eleven.witnesses.map (·.move)).contains w.first)) = true := by
  decide

theorem all_checked : witnesses.all check = true := by decide

theorem all_never (w : Witness) (hw : w ∈ witnesses) :
    ∀ m : Machine, compatible (table w) m → NeverHalts m := by
  have h : check w = true := List.all_eq_true.mp all_checked w hw
  have hparts :
      decide (0 < w.period) = true ∧
        fastSideCycleCheck (table w) w.entry w.period
          w.right w.boundary = true := by
    simpa [check, Bool.and_eq_true] using h
  exact fastSideCycleCheck_sound (table w) w.entry w.period
    w.right w.boundary (of_decide_eq_true hparts.1) hparts.2

#print axioms witness_count
#print axioms pairwise_key_distinct
#print axioms separate_from_first_level
#print axioms all_checked
#print axioms all_never
end BB6.Agent50Raw34Depth2
