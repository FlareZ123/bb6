import Lean

inductive MState where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

structure Cfg where
  st : MState
  head : Nat
  tape : List Bool
  deriving DecidableEq, Repr

/-- One exact transition of the six-state machine in Machine623Path.lean. -/
def step (c : Cfg) : Option Cfg :=
  let b := c.tape.getD c.head false
  match c.st, b with
  | .A, false => some { c with st := .B, head := c.head + 1, tape := c.tape.set c.head true }
  | .A, true  => some { c with st := .E, head := c.head - 1, tape := c.tape.set c.head false }
  | .B, false => some { c with st := .C, head := c.head + 1, tape := c.tape.set c.head false }
  | .B, true  => some { c with st := .C, head := c.head + 1, tape := c.tape.set c.head true }
  | .C, false => some { c with st := .D, head := c.head + 1, tape := c.tape.set c.head false }
  | .C, true  => some { c with st := .A, head := c.head - 1, tape := c.tape.set c.head true }
  | .D, false => some { c with st := .D, head := c.head - 1, tape := c.tape.set c.head true }
  | .D, true  => some { c with st := .A, head := c.head - 1, tape := c.tape.set c.head false }
  | .E, false => some { c with st := .F, head := c.head - 1, tape := c.tape.set c.head true }
  | .E, true  => some { c with st := .C, head := c.head - 1, tape := c.tape.set c.head true }
  | .F, false => none
  | .F, true  => some { c with st := .A, head := c.head - 1, tape := c.tape.set c.head false }

def run : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => match step c with
    | none => none
    | some c' => run n c'

def d2A0Start : Cfg := ⟨.A, 2, [true, true, false, true, true, false, false, false]⟩
def d2A0After : Cfg := ⟨.A, 3, [true, true, true, true, true, false, false, false]⟩

def d3A1Start : Cfg := ⟨.A, 3, [true, false, true, true, false, false, false, false, false]⟩
def d3A1After : Cfg := ⟨.A, 1, [true, false, false, false, false, false, false, false, false]⟩

def d3A0Start : Cfg := ⟨.A, 3, [true, true, true, false, true, false, false, false, false]⟩
def d3A0After : Cfg := ⟨.A, 3, [true, true, true, true, false, true, true, false, false]⟩

def d4A0Start : Cfg := ⟨.A, 4, [true, true, true, true, false, false, false, false, false, false]⟩
def d4A0After : Cfg := ⟨.A, 3, [true, true, true, true, false, true, true, true, false, false]⟩

def d6A1Start : Cfg := ⟨.A, 6, [true, true, true, true, true, true, true, false, false, false]⟩
def d6A1After : Cfg := ⟨.A, 3, [true, true, true, true, true, true, false, false, false, false]⟩

theorem d2_A0_to_d3_A1 : run 3 d2A0Start = some d2A0After := by decide
theorem d3_A1_to_d1_A0 : run 4 d3A1Start = some d3A1After := by decide
theorem d3_A0_to_bad_d3_A1 : run 6 d3A0Start = some d3A0After := by decide
theorem d4_A0_to_bad_d3_A1 : run 7 d4A0Start = some d4A0After := by decide
theorem d6_A1_to_bad_d3_A1 : run 3 d6A1Start = some d6A1After := by decide

def readAt (c : Cfg) (i : Nat) : Bool := c.tape.getD i false

theorem d2_start_prefix_and_right :
    d2A0Start.st = .A ∧ d2A0Start.head = 2 ∧
    readAt d2A0Start 0 = true ∧ readAt d2A0Start 1 = true ∧
    readAt d2A0Start 2 = false ∧ readAt d2A0Start 3 = true ∧ readAt d2A0Start 4 = true := by
  decide

theorem d2_after_is_bad_d3_A1 :
    d2A0After.st = .A ∧ d2A0After.head = 3 ∧
    readAt d2A0After 3 = true ∧ readAt d2A0After 1 = true := by
  decide

theorem d3_A1_after_has_d1_A0_right000 :
    d3A1After.st = .A ∧ d3A1After.head = 1 ∧
    readAt d3A1After 1 = false ∧ readAt d3A1After 2 = false ∧
    readAt d3A1After 3 = false ∧ readAt d3A1After 4 = false := by
  decide

theorem d3_A0_after_is_bad_d3_A1 :
    d3A0After.st = .A ∧ d3A0After.head = 3 ∧
    readAt d3A0After 3 = true ∧ readAt d3A0After 1 = true := by
  decide

theorem d4_A0_after_is_bad_d3_A1 :
    d4A0After.st = .A ∧ d4A0After.head = 3 ∧
    readAt d4A0After 3 = true ∧ readAt d4A0After 1 = true := by
  decide

theorem d6_A1_after_is_bad_d3_A1 :
    d6A1After.st = .A ∧ d6A1After.head = 3 ∧
    readAt d6A1After 3 = true ∧ readAt d6A1After 1 = true := by
  decide
