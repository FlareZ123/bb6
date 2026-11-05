import Lean

namespace BB429Gate94Count

/-- The certified true-root 24-gate residues modulo 2048. This explicit list
    matches BB429Final24.liveClasses and BB429GateArithmetic24.survivors_exact. -/
def root24 : List Nat :=
  [9,73,117,201,209,245,337,465,565,637,765,849,
   949,1021,1033,1097,1141,1233,1361,1673,1789,1917,1973,2045]

/-- All canonical lifts to modulo 8192 (four lifts per 2048 class). -/
def lifts8192 : List Nat :=
  (List.range 4).flatMap (fun q => root24.map (fun r => 2048*q+r))

/-- Remove the two exact whole-family inverse obstructions proved in
    BB429New9Lift.lean, retaining all other lifted possibilities. -/
def live94 : List Nat :=
  lifts8192.filter (fun a => a%8192 != 4105 && a%8192 != 6153)

theorem lift_count : lifts8192.length = 96 := by decide
theorem lift_nodup : lifts8192.Nodup := by decide
theorem lift_after_new_gates_count : live94.length = 94 := by decide
theorem excluded_in_lifts : 4105 ∈ lifts8192 ∧ 6153 ∈ lifts8192 := by decide
theorem removed_both : 4105 ∉ live94 ∧ 6153 ∉ live94 := by decide

#print axioms lift_count
#print axioms lift_nodup
#print axioms lift_after_new_gates_count
#print axioms excluded_in_lifts
#print axioms removed_both
end BB429Gate94Count
