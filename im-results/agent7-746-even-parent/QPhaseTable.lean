import Lean

namespace QPhaseTable

/-- The entry-height formula for the zero-even-reset case. -/
theorem entryFormulaZero (p K z D h : Nat)
    (hD : 18 * D = 32 * p + 20 * K + 34 + z)
    (hEntry : h + D = 8 * p + K) :
    18 * h + 45 + 2 * K + z = 112 * p + 11 := by
  omega

/-- The entry-height formula after exactly one same-level even reset. -/
theorem entryFormulaOne (p K z D h : Nat)
    (hD : 18 * D = 32 * p + 20 * K + 34 + z)
    (hEntry : h + 2 * D = 8 * p + K) :
    18 * h + 68 + 22 * K + 2 * z = 80 * p := by
  omega

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

/-- Since 2^18 = 1 modulo 27, the power term has period 18. -/
theorem pow2m27_period (n : Nat) : pow2m27 (n + 18) = pow2m27 n := by
  unfold pow2m27
  rw [Nat.pow_add]
  have h : 2 ^ 18 % 27 = 1 := by decide
  simp [Nat.mul_mod, h]

/-- The complete K-period is 54: the power has period 18 and the linear terms period 27. -/
theorem W0_periodK (K j : Nat) : W0m27 (K + 54) j = W0m27 K j := by
  have hp : pow2m27 (K + 54) = pow2m27 K := by
    calc
      pow2m27 (K + 54) = pow2m27 ((K + 36) + 18) := by congr 1 <;> omega
      _ = pow2m27 (K + 36) := pow2m27_period (K + 36)
      _ = pow2m27 ((K + 18) + 18) := by congr 1 <;> omega
      _ = pow2m27 (K + 18) := pow2m27_period (K + 18)
      _ = pow2m27 K := pow2m27_period K
  have hk1 : (2 * (K + 54)) % 27 = (2 * K) % 27 := by omega
  have hk2 : (2 * (K + 54) + 7) % 27 = (2 * K + 7) % 27 := by omega
  simp [W0m27, add27, sub27, mul27, hp, hk1, hk2]

theorem W1_periodK (K j : Nat) : W1m27 (K + 54) j = W1m27 K j := by
  have hp : pow2m27 (K + 54) = pow2m27 K := by
    calc
      pow2m27 (K + 54) = pow2m27 ((K + 36) + 18) := by congr 1 <;> omega
      _ = pow2m27 (K + 36) := pow2m27_period (K + 36)
      _ = pow2m27 ((K + 18) + 18) := by congr 1 <;> omega
      _ = pow2m27 (K + 18) := pow2m27_period (K + 18)
      _ = pow2m27 K := pow2m27_period K
  have hk1 : (22 * (K + 54) + 23) % 27 = (22 * K + 23) % 27 := by omega
  have hk2 : (2 * (2 * (K + 54) + 7)) % 27 = (2 * (2 * K + 7)) % 27 := by omega
  simp [W1m27, sub27, mul27, hp, hk1, hk2]

theorem W0_periodJ (K j : Nat) : W0m27 K (j + 18) = W0m27 K j := by
  have harg : j + 18 + 4 = (j + 4) + 18 := by omega
  unfold W0m27
  rw [harg, pow2m27_period]

theorem W1_periodJ (K j : Nat) : W1m27 K (j + 18) = W1m27 K j := by
  have harg : j + 18 + 4 = (j + 4) + 18 := by omega
  unfold W1m27
  rw [harg, pow2m27_period]

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
