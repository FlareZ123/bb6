import Lean

namespace TailWindow

open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

inductive Dir where
  | L | R
  deriving DecidableEq, Repr

def dx : Dir → Int
  | .L => -1
  | .R => 1

/-- Exact standard six-state, two-symbol TM62/D0 table. -/
def instr : Nat → Bool → Option (Bool × Dir × Nat)
  | 0, false => some (true, .R, 1)
  | 0, true  => some (false, .R, 4)
  | 1, false => some (true, .L, 2)
  | 1, true  => some (false, .R, 0)
  | 2, false => some (true, .L, 0)
  | 2, true  => some (true, .L, 3)
  | 3, false => some (true, .L, 2)
  | 3, true  => some (true, .L, 5)
  | 4, false => some (false, .L, 2)
  | 4, true  => some (false, .L, 1)
  | 5, false => some (true, .L, 4)
  | 5, true  => none
  | _, _ => none

structure Cfg where
  state : Nat
  pos : Int
  tape : Int → Bool

def updateTape (t : Int → Bool) (p : Int) (w : Bool) : Int → Bool :=
  fun i => if i = p then w else t i

def step (c : Cfg) : Option Cfg :=
  match instr c.state (c.tape c.pos) with
  | none => none
  | some (w, d, s) =>
      some ⟨s, c.pos + dx d, updateTape c.tape c.pos w⟩

def run : Nat → Option Cfg → Option Cfg
  | 0, c => c
  | n + 1, c => run n (c.bind step)

@[simp] theorem run_none (n : Nat) : run n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, ih]

theorem run_succ_right (n : Nat) (c : Option Cfg) :
    run (n + 1) c = (run n c).bind step := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      change run (n + 1) (c.bind step) = (run n (c.bind step)).bind step
      exact ih (c.bind step)

/-- Canonical DRegular suffix (01)^q 1^b. -/
def suffix : Nat → Nat → List Bool
  | 0, b => List.replicate b true
  | q + 1, b => false :: true :: suffix q b

def tailPrefix : List Bool := [true, false, true, true, false, true, true]

def rightCells (q b : Nat) : List Bool := tailPrefix ++ suffix q b

def localTape (q b : Nat) : Int → Bool := fun i =>
  if i < 0 then
    ([false, false, true, false, true] : List Bool).getD ((-i - 1).toNat) false
  else if i = 0 then false
  else (rightCells q b).getD (i.toNat - 1) false

def pairBlock : Nat → List Bool
  | 0 => []
  | n + 1 => true :: false :: pairBlock n

def actualLeft (m : Nat) : List Bool :=
  [false, false] ++ pairBlock m ++ [true, true]

def actualTape (m q b : Nat) : Int → Bool := fun i =>
  if i < 0 then
    (actualLeft m).getD ((-i - 1).toNat) false
  else if i = 0 then false
  else (rightCells q b).getD (i.toNat - 1) false

def startLocal (q b : Nat) : Cfg := ⟨4, 0, localTape q b⟩
def startActual (m q b : Nat) : Cfg := ⟨4, 0, actualTape m q b⟩

def inWindow (lo hi : Int) (c : Cfg) : Bool := decide (lo ≤ c.pos ∧ c.pos ≤ hi)

def within : Nat → Option Cfg → Int → Int → Bool
  | 0, none, _, _ => true
  | 0, some c, lo, hi => inWindow lo hi c
  | n + 1, none, _, _ => true
  | n + 1, some c, lo, hi => inWindow lo hi c && within n (step c) lo hi

def Stays (lo hi : Int) : Nat → Option Cfg → Prop
  | 0, none => True
  | 0, some c => lo ≤ c.pos ∧ c.pos ≤ hi
  | n + 1, none => True
  | n + 1, some c => (lo ≤ c.pos ∧ c.pos ≤ hi) ∧ Stays lo hi n (step c)

theorem within_iff_Stays (lo hi : Int) (n : Nat) (c : Option Cfg) :
    within n c lo hi = true ↔ Stays lo hi n c := by
  induction n generalizing c with
  | zero => cases c <;> simp [within, Stays, inWindow]
  | succ n ih =>
      cases c with
      | none => simp [within, Stays]
      | some c =>
          simp [within, Stays, inWindow, ih]

theorem stays_run_pos (lo hi : Int) (n : Nat) (c : Option Cfg)
    (h : Stays lo hi n c) :
    match run n c with
    | none => True
    | some d => lo ≤ d.pos ∧ d.pos ≤ hi := by
  induction n generalizing c with
  | zero => cases c <;> simpa [run, Stays] using h
  | succ n ih =>
      cases c with
      | none => simp [run]
      | some c0 =>
          rcases h with ⟨_, htail⟩
          simpa [run] using ih (step c0) htail

def ConfigEqOn (lo hi : Int) (c₁ c₂ : Cfg) : Prop :=
  c₁.state = c₂.state ∧ c₁.pos = c₂.pos ∧
    ∀ i, lo ≤ i → i ≤ hi → c₁.tape i = c₂.tape i

def OptionEqOn (lo hi : Int) : Option Cfg → Option Cfg → Prop
  | none, none => True
  | some c₁, some c₂ => ConfigEqOn lo hi c₁ c₂
  | _, _ => False

theorem stepEqOn (lo hi : Int) (c₁ c₂ : Cfg)
    (hEq : ConfigEqOn lo hi c₁ c₂)
    (hpos : lo ≤ c₁.pos ∧ c₁.pos ≤ hi) :
    OptionEqOn lo hi (step c₁) (step c₂) := by
  rcases hEq with ⟨hs, hp, ht⟩
  have hread : c₁.tape c₁.pos = c₂.tape c₁.pos := ht c₁.pos hpos.1 hpos.2
  unfold step
  rw [← hs, ← hp, ← hread]
  cases hinst : instr c₁.state (c₁.tape c₁.pos) with
  | none => simp [hinst, OptionEqOn]
  | some ins =>
      rcases ins with ⟨w, d, s⟩
      cases d <;> simp only [hinst, OptionEqOn, ConfigEqOn, updateTape, dx, true_and]
      all_goals
        intro i hlow hhigh
        by_cases hi : i = c₁.pos
        · simp [updateTape, hi]
        · simp [updateTape, hi, ht i hlow hhigh]

theorem runEqOn (lo hi : Int) (n : Nat) (c₁ c₂ : Option Cfg)
    (hEq : OptionEqOn lo hi c₁ c₂)
    (hStay : Stays lo hi n c₁) :
    OptionEqOn lo hi (run n c₁) (run n c₂) := by
  induction n generalizing c₁ c₂ with
  | zero => simpa [run] using hEq
  | succ n ih =>
      cases c₁ with
      | none =>
          cases c₂ with
          | none => simp [run, OptionEqOn]
          | some b => simp [OptionEqOn] at hEq
      | some a =>
          cases c₂ with
          | none => simp [OptionEqOn] at hEq
          | some b =>
              rcases hEq with ⟨hs, hp, ht⟩
              rcases hStay with ⟨⟨hlo, hhi⟩, htail⟩
              have hstep := stepEqOn lo hi a b ⟨hs, hp, ht⟩ ⟨hlo, hhi⟩
              simpa [run] using ih (step a) (step b) hstep htail

/-- First five cells of the actual left stack agree with the local window. -/
theorem actualLeft_prefix (m : Nat) (hm : 3 ≤ m) :
    (actualLeft m).take 5 = [false, false, true, false, true] := by
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m => simp [actualLeft, pairBlock]

theorem initialEqOn (m q b maxRight : Nat) (hm : 3 ≤ m) :
    ConfigEqOn (-5) (maxRight : Int) (startActual m q b) (startLocal q b) := by
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m =>
        constructor
        · rfl
        constructor
        · rfl
        · intro i hlo hhi
          by_cases hneg : i < 0
          · have hi : i = -5 ∨ i = -4 ∨ i = -3 ∨ i = -2 ∨ i = -1 := by omega
            rcases hi with h | h | h | h | h <;> subst i <;>
              simp [startActual, startLocal, actualTape, localTape, actualLeft, pairBlock]
          · by_cases hz : i = 0
            · subst i
              simp [startActual, startLocal, actualTape, localTape]
            · have hpos : 0 < i := by omega
              simp [startActual, startLocal, actualTape, localTape, rightCells, hneg, hz, hpos]

end TailWindow
