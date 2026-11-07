import Lean

namespace S4PrefixReturn8Standalone

def hp (a : Nat) : List Nat → List Nat
  | [] => [if a % 2 = 0 then a / 2 + 2 else a / 2]
  | b :: xs =>
      if a % 2 = 0 then (a / 2 + 2) :: (b + a / 2) :: xs
      else (a / 2) :: hp (b + a / 2 + 1) xs

def gp (c : Nat) : List Nat → List Nat
  | [] => []
  | b :: xs => hp (b + c) xs

def pp (xs : List Nat) : List Nat := gp 219 (gp 290 (gp 509 xs))

def prefixRun : Nat → List Nat → List Nat
  | 0, xs => xs
  | n+1, xs => pp (prefixRun n xs)

def cycle7 : List Nat := [283,906,982,3490,3734,5935,13580]

def return8 (v : Nat) : Nat := (prefixRun 5120 (cycle7 ++ [v])).getLast!

set_option maxRecDepth 250000
set_option maxHeartbeats 0

theorem r25036 : return8 25036 = 109210 := by decide
theorem r109210 : return8 109210 = 109208 := by decide
theorem r109208 : return8 109208 = 109209 := by decide
theorem r109209 : return8 109209 = 109206 := by decide
theorem r109206 : return8 109206 = 109210 := by decide

#print axioms r25036
#print axioms r109210
#print axioms r109208
#print axioms r109209
#print axioms r109206

end S4PrefixReturn8Standalone
