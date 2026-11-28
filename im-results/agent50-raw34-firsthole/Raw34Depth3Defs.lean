import Raw34ElevenSideCycles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Raw34Depth3
open BB6Coverage BB6Coverage.Agent50SideCycle
structure Witness where
  first : Move
  secondSlot : Slot
  second : Move
  thirdSlot : Slot
  third : Move
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
  deriving DecidableEq

def table (w : Witness) : PartialMachine :=
  BB6Coverage.refine
    (BB6Coverage.refine
      (BB6.Agent50Raw34Eleven.child w.first) w.secondSlot (some w.second))
      w.thirdSlot (some w.third)
def check (w : Witness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w) w.entry w.period w.right w.boundary

theorem check_sound (w : Witness) (h : check w = true)
    (m : Machine) (hm : compatible (table w) m) : NeverHalts m := by
  have parts :
      decide (0 < w.period) = true ∧
        fastSideCycleCheck (table w) w.entry w.period
          w.right w.boundary = true := by
    simpa [check,Bool.and_eq_true] using h
  exact fastSideCycleCheck_sound (table w) w.entry w.period
    w.right w.boundary (of_decide_eq_true parts.1) parts.2 m hm
#print axioms check_sound
end BB6.Agent50Raw34Depth3
