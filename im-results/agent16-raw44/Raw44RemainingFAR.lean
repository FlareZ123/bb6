import FastFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44RemainingFAR
open BB6Coverage BB6Coverage.FAR

theorem try_sound (p : PartialMachine) {d : Nat} (start : Fin d) (dfa : List (Fin d))
    (hc : (fastTryDfa p start dfa).isSome = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  cases h : fastTryDfa p start dfa with
  | none => simp [h] at hc
  | some v => exact v.2.1.sound p v.2.2 m hm

namespace C1LELeaf3
-- 1RB---_1RC0RC_0RD1LE_1LD1LB_0LA1RF_0LD0RF
def table : PartialMachine := fromCodes [7,24,11,9,13,18,14,6,0,23,12,21]
def dfa : List (Fin 3) := [0,1,2,1,1,1]
theorem checked : (fastTryDfa (reflectPartial table) 0 dfa).isSome = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  reflectNever m (try_sound (reflectPartial table) 0 dfa checked (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end C1LELeaf3

namespace C1LELeaf6
-- 1RB0LE_1RC0RC_0RD1LE_1LD1LB_1LA0RF_---0RC
def table : PartialMachine := fromCodes [7,16,11,9,13,18,14,6,2,21,24,9]
def dfa : List (Fin 4) := [0,1,1,2,1,3,2,3]
theorem checked : (fastTryDfa (reflectPartial table) 0 dfa).isSome = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  reflectNever m (try_sound (reflectPartial table) 0 dfa checked (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end C1LELeaf6

namespace C1LELeaf7
-- 1RB0LF_1RC0RC_0RD1LE_1LD1LB_1LA0RB_1LA---
def table : PartialMachine := fromCodes [7,20,11,9,13,18,14,6,2,5,2,24]
def dfa : List (Fin 4) := [0,1,1,2,1,3,2,3]
theorem checked : (fastTryDfa (reflectPartial table) 0 dfa).isSome = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  reflectNever m (try_sound (reflectPartial table) 0 dfa checked (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end C1LELeaf7

namespace C1LELeaf19
-- 1RB1LF_1RC0RC_0RD1LE_1LD1LB_1LF0RB_0LA---
def table : PartialMachine := fromCodes [7,22,11,9,13,18,14,6,22,5,0,24]
def dfa : List (Fin 4) := [0,1,2,1,3,1,0,1]
theorem checked : (fastTryDfa (reflectPartial table) 0 dfa).isSome = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  reflectNever m (try_sound (reflectPartial table) 0 dfa checked (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end C1LELeaf19

namespace C1LELeaf21
-- 1RB1RA_1RC0RC_0RD1LE_1LD1LB_1LF---_0RA0LF
def table : PartialMachine := fromCodes [7,3,11,9,13,18,14,6,22,24,1,20]
def dfa : List (Fin 6) := [0,1,0,2,3,4,0,1,5,5,0,1]
theorem checked : (fastTryDfa table 0 dfa).isSome = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  try_sound table 0 dfa checked m hm
#print axioms never
end C1LELeaf21

namespace C1RELeaf3
-- 1RB1LF_1RC0RC_0RD1RE_1LD1LB_0LA1LB_1LA---
def table : PartialMachine := fromCodes [7,22,11,9,13,19,14,6,0,6,2,24]
def dfa : List (Fin 4) := [0,1,2,3,2,1,2,1]
theorem checked : (fastTryDfa (reflectPartial table) 0 dfa).isSome = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  reflectNever m (try_sound (reflectPartial table) 0 dfa checked (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end C1RELeaf3

namespace C1RELeaf4
-- 1RB---_1RC0RC_0RD1RE_1LD1LB_0LF1LB_0LA1LF
def table : PartialMachine := fromCodes [7,24,11,9,13,19,14,6,20,6,0,22]
def dfa : List (Fin 5) := [0,1,2,3,4,1,4,1,3,1]
theorem checked : (fastTryDfa (reflectPartial table) 0 dfa).isSome = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  reflectNever m (try_sound (reflectPartial table) 0 dfa checked (reflectTable m) (reflectCompatible table m hm))
#print axioms never
end C1RELeaf4

end BB6.Agent16Raw44RemainingFAR
