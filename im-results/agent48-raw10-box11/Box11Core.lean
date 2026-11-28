import PackedFinite

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48Box11
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge BB6.Agent48Box12
open BB6.Agent49Box (Box Fits)
open BB6.Agent49Box6 (index decode code fromCodes partialEq_sound)

def initial : PartialMachine := fromCodes #[8,25,11,25,17,13,11,25,25,25,25,25]
def b1Codes : List Nat := [0,1,2,3,4,8,10,12,13,14,15,16,17,18,19,20,21,22,23,24]
def e0Codes : List Nat := [0,2,3,4,12,18,20,21,22,23,24]
def baseBox : Box Slot Transition := fun s =>
  match initial s with
  | some t => [t]
  | none => if index s = 3 then b1Codes.map decode else if index s = 8 then e0Codes.map decode else choices

theorem initial_compatible (m : Machine) (hm : Fits baseBox m) : compatible initial m := by
  intro s t h
  have hs := hm s
  simpa [baseBox,h] using hs

def sourceMatch (b : Box Slot Transition) : Bool :=
  slots.all fun s => transitions.all fun t => decide ((t ∈ b s) ↔ (t ∈ baseBox s))
theorem sourceIndex11 : sourceMatch raw10Remainder[11]! = true := by decide +kernel
theorem sourceMatch_sound (b : Box Slot Transition) (h : sourceMatch b=true)
    (m : Machine) (hm : Fits b m) : Fits baseBox m := by
  intro s
  have hs := List.all_eq_true.mp h s (slots_complete s)
  have ht := List.all_eq_true.mp hs (m s) (transitions_complete (m s))
  exact (of_decide_eq_true ht).mp (hm s)

def e0zero : PartialMachine := fromCodes #[8,25,11,25,17,13,11,25,0,25,25,25]
theorem zero_bound (m : Machine) (hm : compatible e0zero m) : WeightedBound 11 m :=
  ordinary_weighted 11 6 (by decide) m (haltCheck_sound 6 e0zero 5 (by decide +kernel) m hm)
theorem source_zero_bound (m : Machine) (hm : Fits raw10Remainder[11]! m)
    (he : m (4,false) = decode 0) : WeightedBound 11 m := by
  have hb := sourceMatch_sound _ sourceIndex11 m hm
  have hi := initial_compatible m hb
  have hr := compatible_refine initial m (4,false) hi
  rw [he,show refine initial (4,false) (decode 0) = e0zero from partialEq_sound (by decide +kernel)] at hr
  exact zero_bound m hr

#print axioms sourceIndex11
#print axioms source_zero_bound
end BB6.Agent48Box11
