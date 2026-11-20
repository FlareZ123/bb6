import Lean

namespace BB6PostResetCarry

structure State where
  px : Fin 3
  py : Fin 3
  la : Fin 2
  ra : Fin 4
deriving DecidableEq, Repr, Fintype

def leftA (c : Fin 2) : Int := if c.val = 0 then -1 else 0
def rightA (c : Fin 4) : Int := match c.val with | 0 => -1 | 1 => -2 | 2 => -2 | _ => -3
def rightB (c : Fin 4) : Int := match c.val with | 0 => 0 | 1 => 0 | 2 => 1 | _ => 1
def encodeLeft (a : Int) : Fin 2 := if a = -1 then 0 else 1
def encodeRight (a b : Int) : Fin 4 :=
  if a = -1 ∧ b = 0 then 0
  else if a = -2 ∧ b = 0 then 1
  else if a = -2 ∧ b = 1 then 2
  else 3

def floorDiv3 (n : Int) : Int :=
  if n < 0 then - ((-n + 2) / (3 : Int)) else n / (3 : Int)

def leftNext (s : State) (x : Fin 3) : Int :=
  floorDiv3 ((Int.ofNat x.val) - (Int.ofNat s.py.val) + leftA s.la)
def rightANext (s : State) (x : Fin 3) : Int :=
  floorDiv3 (-(Int.ofNat x.val) - (Int.ofNat s.px.val) - (Int.ofNat s.py.val) + rightA s.ra)
def rightBNext (s : State) : Int :=
  floorDiv3 ((Int.ofNat s.px.val) + (Int.ofNat s.py.val) + rightB s.ra)

def step (s : State) (x y : Fin 3) : State :=
  ⟨x, y, encodeLeft (leftNext s x), encodeRight (rightANext s x) (rightBNext s)⟩

def Allowed (s : State) : Prop :=
  ¬ (s.px.val = 0 ∧ s.la.val = 1 ∧ s.ra.val = 3) ∧
  ¬ (s.px.val = 2 ∧ s.la.val = 0 ∧ s.ra.val = 0)

def Seed (s : State) : Prop :=
  match s.px.val, s.la.val, s.ra.val with
  | 0, 0, 0 => True
  | 0, 0, 1 => True
  | 0, 0, 2 => True
  | 0, 0, 3 => True
  | 0, 1, 0 => True
  | 0, 1, 2 => True
  | 1, 0, 1 => True
  | 1, 0, 2 => True
  | 1, 0, 3 => True
  | 1, 1, 0 => True
  | 1, 1, 1 => True
  | 1, 1, 2 => True
  | 2, 0, 1 => True
  | 2, 0, 3 => True
  | 2, 1, 0 => True
  | 2, 1, 1 => True
  | 2, 1, 2 => True
  | 2, 1, 3 => True
  | _, _, _ => False

def allStates : List State := [
  ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 1, 1⟩, ⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 1, 0, 0⟩,
  ⟨0, 1, 0, 1⟩, ⟨0, 1, 0, 2⟩, ⟨0, 1, 0, 3⟩, ⟨0, 1, 1, 0⟩, ⟨0, 1, 1, 1⟩, ⟨0, 1, 1, 2⟩, ⟨0, 1, 1, 3⟩, ⟨0, 2, 0, 0⟩, ⟨0, 2, 0, 1⟩,
  ⟨0, 2, 0, 2⟩, ⟨0, 2, 0, 3⟩, ⟨0, 2, 1, 0⟩, ⟨0, 2, 1, 1⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 1, 3⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 1⟩, ⟨1, 0, 0, 2⟩,
  ⟨1, 0, 0, 3⟩, ⟨1, 0, 1, 0⟩, ⟨1, 0, 1, 1⟩, ⟨1, 0, 1, 2⟩, ⟨1, 0, 1, 3⟩, ⟨1, 1, 0, 0⟩, ⟨1, 1, 0, 1⟩, ⟨1, 1, 0, 2⟩, ⟨1, 1, 0, 3⟩,
  ⟨1, 1, 1, 0⟩, ⟨1, 1, 1, 1⟩, ⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨1, 2, 0, 0⟩, ⟨1, 2, 0, 1⟩, ⟨1, 2, 0, 2⟩, ⟨1, 2, 0, 3⟩, ⟨1, 2, 1, 0⟩,
  ⟨1, 2, 1, 1⟩, ⟨1, 2, 1, 2⟩, ⟨1, 2, 1, 3⟩, ⟨2, 0, 0, 0⟩, ⟨2, 0, 0, 1⟩, ⟨2, 0, 0, 2⟩, ⟨2, 0, 0, 3⟩, ⟨2, 0, 1, 0⟩, ⟨2, 0, 1, 1⟩,
  ⟨2, 0, 1, 2⟩, ⟨2, 0, 1, 3⟩, ⟨2, 1, 0, 0⟩, ⟨2, 1, 0, 1⟩, ⟨2, 1, 0, 2⟩, ⟨2, 1, 0, 3⟩, ⟨2, 1, 1, 0⟩, ⟨2, 1, 1, 1⟩, ⟨2, 1, 1, 2⟩,
  ⟨2, 1, 1, 3⟩, ⟨2, 2, 0, 0⟩, ⟨2, 2, 0, 1⟩, ⟨2, 2, 0, 2⟩, ⟨2, 2, 0, 3⟩, ⟨2, 2, 1, 0⟩, ⟨2, 2, 1, 1⟩, ⟨2, 2, 1, 2⟩, ⟨2, 2, 1, 3⟩
]
def allowedStates : List State := allStates.filter Allowed

def resetOutputLabels : List State := [
  ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 2, 0, 0⟩, ⟨2, 0, 1, 1⟩, ⟨2, 1, 1, 1⟩, ⟨2, 2, 1, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 1, 0, 2⟩, ⟨0, 2, 0, 2⟩,
  ⟨2, 0, 1, 3⟩, ⟨2, 1, 1, 3⟩, ⟨2, 2, 1, 3⟩, ⟨1, 0, 1, 0⟩, ⟨1, 1, 1, 0⟩, ⟨1, 2, 1, 0⟩, ⟨1, 0, 0, 2⟩, ⟨1, 1, 0, 2⟩, ⟨1, 2, 0, 2⟩,
  ⟨1, 0, 0, 3⟩, ⟨1, 1, 0, 3⟩, ⟨1, 2, 0, 3⟩, ⟨1, 0, 1, 1⟩, ⟨1, 1, 1, 1⟩, ⟨1, 2, 1, 1⟩, ⟨1, 0, 1, 2⟩, ⟨1, 1, 1, 2⟩, ⟨1, 2, 1, 2⟩,
  ⟨1, 0, 0, 1⟩, ⟨1, 1, 0, 1⟩, ⟨1, 2, 0, 1⟩, ⟨2, 0, 0, 1⟩, ⟨2, 1, 0, 1⟩, ⟨2, 2, 0, 1⟩, ⟨0, 0, 0, 1⟩, ⟨0, 1, 0, 1⟩, ⟨0, 2, 0, 1⟩,
  ⟨2, 0, 0, 3⟩, ⟨2, 1, 0, 3⟩, ⟨2, 2, 0, 3⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨2, 0, 1, 0⟩, ⟨2, 1, 1, 0⟩, ⟨2, 2, 1, 0⟩,
  ⟨2, 0, 1, 2⟩, ⟨2, 1, 1, 2⟩, ⟨2, 2, 1, 2⟩, ⟨0, 0, 1, 2⟩, ⟨0, 1, 1, 2⟩, ⟨0, 2, 1, 2⟩, ⟨0, 0, 0, 3⟩, ⟨0, 1, 0, 3⟩, ⟨0, 2, 0, 3⟩
]

theorem allStates_nodup : allStates.Nodup := by decide
theorem allStates_length : allStates.length = 72 := by decide
theorem allowedStates_length : allowedStates.length = 66 := by decide
theorem allowedStates_complete (s : State) : Allowed s ↔ s ∈ allowedStates := by decide
theorem resetOutputLabels_nodup : resetOutputLabels.Nodup := by decide
theorem resetOutputLabels_length : resetOutputLabels.length = 54 := by decide
theorem resetOutputLabels_are_seed (s : State) : s ∈ resetOutputLabels ↔ Seed s := by decide
theorem seed_subset_allowed (s : State) : Seed s → Allowed s := by decide

theorem leftNext_valid (s : State) (h : Allowed s) (x : Fin 3) :
    leftNext s x = -1 ∨ leftNext s x = 0 := by decide
theorem rightNext_valid (s : State) (h : Allowed s) (x : Fin 3) :
    (rightANext s x = -1 ∧ rightBNext s = 0) ∨
    (rightANext s x = -2 ∧ rightBNext s = 0) ∨
    (rightANext s x = -2 ∧ rightBNext s = 1) ∨
    (rightANext s x = -3 ∧ rightBNext s = 1) := by decide

/-- Exact 66-state paired carry closure under every raw digit-pair input. -/
theorem allowed_step (s : State) (h : Allowed s) (x y : Fin 3) :
    Allowed (step s x y) := by decide

theorem reset_output_step_closed (s : State) (hs : s ∈ resetOutputLabels)
    (x y : Fin 3) : step s x y ∈ allowedStates := by
  apply (allowedStates_complete _).2
  exact allowed_step s (seed_subset_allowed s ((resetOutputLabels_are_seed s).1 hs)) x y

#print axioms allowed_step
#print axioms reset_output_step_closed

end BB6PostResetCarry
