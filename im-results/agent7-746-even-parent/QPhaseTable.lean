import Lean

namespace QPhaseTable

def add27 (a b : Nat) : Nat := (a % 27 + b % 27) % 27
def sub27 (a b : Nat) : Nat := (a % 27 + 27 - b % 27) % 27
def mul27 (a b : Nat) : Nat := (a % 27 * (b % 27)) % 27
def pow2m27 (n : Nat) : Nat := 2 ^ n % 27

def W0m27 (K j : Nat) : Nat :=
  sub27 (add27 (mul27 112 (pow2m27 K)) 11)
    (add27 (2 * K) (mul27 (2 * K + 7) (pow2m27 (j + 4))))

def W1m27 (K j : Nat) : Nat :=
  sub27 (sub27 (mul27 80 (pow2m27 K)) (22 * K + 23))
    (mul27 (2 * (2 * K + 7)) (pow2m27 (j + 4)))

def candidates0 (K : Nat) : List Nat :=
  (List.range 9).filterMap (fun r => if W0m27 K (2 * r) = 0 then some (2 * r) else none)

def candidates1 (K : Nat) : List Nat :=
  (List.range 9).filterMap (fun r => if W1m27 K (2 * r) = 0 then some (2 * r) else none)

example : candidates0 2 = [12] := by decide
example : candidates0 3 = [12] := by decide
example : candidates0 8 = [10] := by decide
example : candidates0 9 = [8] := by decide
example : candidates0 14 = [8] := by decide
example : candidates0 15 = [4] := by decide
example : candidates0 20 = [6] := by decide
example : candidates0 21 = [0] := by decide
example : candidates0 26 = [4] := by decide
example : candidates0 27 = [14] := by decide
example : candidates0 32 = [2] := by decide
example : candidates0 33 = [10] := by decide
example : candidates0 38 = [0] := by decide
example : candidates0 39 = [6] := by decide
example : candidates0 44 = [16] := by decide
example : candidates0 45 = [2] := by decide
example : candidates0 50 = [14] := by decide
example : candidates0 51 = [16] := by decide

example : candidates1 2 = [6] := by decide
example : candidates1 3 = [0] := by decide
example : candidates1 8 = [4] := by decide
example : candidates1 9 = [14] := by decide
example : candidates1 14 = [2] := by decide
example : candidates1 15 = [10] := by decide
example : candidates1 20 = [0] := by decide
example : candidates1 21 = [6] := by decide
example : candidates1 26 = [16] := by decide
example : candidates1 27 = [2] := by decide
example : candidates1 32 = [14] := by decide
example : candidates1 33 = [16] := by decide
example : candidates1 38 = [12] := by decide
example : candidates1 39 = [12] := by decide
example : candidates1 44 = [10] := by decide
example : candidates1 45 = [8] := by decide
example : candidates1 50 = [8] := by decide
example : candidates1 51 = [4] := by decide

end QPhaseTable
