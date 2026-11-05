import Lean

namespace BB429Count58

def live24 : List Nat :=
  [9,73,117,201,209,245,337,465,565,637,765,849,
   949,1021,1033,1097,1141,1233,1361,1673,1789,1917,1973,2045]

def excluded38 : List Nat :=
  [73,117,949,1033,1361,1917,2045,2121,2293,2613,2813,2997,
   3721,3837,4093,4105,4433,4561,4861,5193,5237,5329,
   5769,5885,6069,6153,6261,6353,6481,6609,6781,6993,
   7177,7241,7285,7377,7505,8117]

def lifts96 : List Nat :=
  (List.range 4).flatMap (fun k => live24.map (fun r => 2048*k+r))

def live58 : List Nat := lifts96.filter (fun r => !excluded38.contains r)

theorem lifts96_count : lifts96.length=96 := by decide
theorem lifts96_nodup : lifts96.Nodup := by decide
theorem live58_count : live58.length=58 := by decide
theorem live58_nodup : live58.Nodup := by decide

#print axioms live58_count
end BB429Count58
