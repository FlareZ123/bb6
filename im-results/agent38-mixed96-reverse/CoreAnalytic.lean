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

def lowA1 (a k : Nat) : Prop :=
  (a % 48 = 18 ∧ k % 24 = 22) ∨
  (a % 48 = 20 ∧ k % 24 = 23) ∨
  (a % 48 = 42 ∧ k % 24 = 10)

def lowB0 (a k : Nat) : Prop :=
  (a % 48 = 4 ∧ k % 24 = 16) ∨
  (a % 48 = 18 ∧ k % 24 = 7) ∨
  (a % 48 = 42 ∧ k % 24 = 19)

def lowB1 (a k : Nat) : Prop :=
  (a % 48 = 4 ∧ k % 24 = 15) ∨
  (a % 48 = 18 ∧ k % 24 = 6) ∨
  (a % 48 = 42 ∧ k % 24 = 18)

def coreA (a k c : Nat) : Prop :=
  match c with
  | 0 => lowA0 a k
  | 1 => lowA1 a k
  | _ => highA (normX a c) (normY k c)

def coreB (a k c : Nat) : Prop :=
  match c with
  | 0 => lowB0 a k
  | 1 => lowB1 a k
  | _ => highB (normX a c) (normY k c)

theorem coreA_blank_false : ¬coreA 5 0 1 := by decide
theorem coreB_blank_false : ¬coreB 5 0 1 := by decide

theorem normX_shift (a c : Nat) (ha : 1 ≤ a) (hc : 4 ≤ c) :
    normX (a - 1) (c - 1) = normX a c := by
  unfold normX
  omega

theorem normY_shift (k c : Nat) (hc : 4 ≤ c) :
    normY (k + 1) (c - 1) = normY k c := by
  unfold normY
  omega

#print axioms normX_shift
#print axioms normY_shift

theorem coreA_high (a k c : Nat) (hc : 2 ≤ c) :
    coreA a k c ↔ highA (normX a c) (normY k c) := by
  cases c with
  | zero => omega
  | succ c =>
    cases c with
    | zero => omega
    | succ c => rfl

theorem coreB_high (a k c : Nat) (hc : 2 ≤ c) :
    coreB a k c ↔ highB (normX a c) (normY k c) := by
  cases c with
  | zero => omega
  | succ c =>
    cases c with
    | zero => omega
    | succ c => rfl

theorem coreA_regular (a k c : Nat) (ha : 1 ≤ a) (hc : 4 ≤ c) :
    coreA (a - 1) (k + 1) (c - 1) ↔ coreA a k c := by
  rw [coreA_high (a - 1) (k + 1) (c - 1) (by omega)]
  rw [coreA_high a k c (by omega)]
  rw [normX_shift a c ha hc, normY_shift k c hc]

theorem coreB_regular (a k c : Nat) (ha : 1 ≤ a) (hc : 4 ≤ c) :
    coreB (a - 1) (k + 1) (c - 1) ↔ coreB a k c := by
  rw [coreB_high (a - 1) (k + 1) (c - 1) (by omega)]
  rw [coreB_high a k c (by omega)]
  rw [normX_shift a c ha hc, normY_shift k c hc]

#print axioms coreA_regular
#print axioms coreB_regular

end A38Mixed96
