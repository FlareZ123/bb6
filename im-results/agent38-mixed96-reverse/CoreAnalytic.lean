import Std
namespace A38Mixed96

def normX (a c : Nat) : Nat := (a + 96 - ((c - 2) % 96)) % 96
def normY (k c : Nat) : Nat := (k + ((c - 2) % 96)) % 96

def highA (x y : Nat) : Prop :=
  (x % 48 = 2 ∧ y % 24 = 5) ∨
  (x = 12 ∧ y = 29) ∨ (x = 60 ∧ y = 77) ∨
  (x % 48 = 17 ∧ y % 24 = 21) ∨
  (x % 48 = 19 ∧ (y % 48 = 0 ∨ y % 48 = 22 ∨ y % 48 = 46)) ∨
  (x % 48 = 26 ∧ y % 24 = 17) ∨
  (x % 48 = 41 ∧ y % 24 = 9)

def highB (x y : Nat) : Prop :=
  (x % 48 = 3 ∧ y % 24 = 14) ∨
  (x % 48 = 10 ∧ y % 24 = 9) ∨
  (x % 48 = 17 ∧ y % 24 = 5) ∨
  (x % 48 = 19 ∧ y % 48 = 32) ∨
  (x = 28 ∧ y = 77) ∨ (x = 76 ∧ y = 29) ∨
  (x % 48 = 34 ∧ y % 24 = 21) ∨
  (x % 48 = 41 ∧ y % 24 = 17)

def lowA0 (a k : Nat) : Prop :=
  (a % 48 = 18 ∧ k % 24 = 23) ∨
  (a % 48 = 20 ∧ k % 24 = 0) ∨
  (a % 48 = 42 ∧ k % 24 = 11)

end A38Mixed96
