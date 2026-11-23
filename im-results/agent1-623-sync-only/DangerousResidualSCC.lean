import Lean

namespace BB6DangerousResidualSCC

theorem left_residual_identity (g q gamma : Int) :
    (2 * g - gamma) - 3 * (6 * q) = 2 * (g - 9 * q) - gamma := by
  omega

theorem right_residual_identity (g q gamma : Int) :
    4 * (2 * g - gamma) + 3 * (6 * q) =
      2 * (4 * g + 9 * q) - 4 * gamma := by
  omega

structure Edge where
  src : Nat
  x : Int
  y : Int
  dst : Nat
  deriving DecidableEq, Repr

def leftEdges : List Edge := [
  ⟨54,0,0,54⟩, ⟨54,0,1,55⟩, ⟨54,0,2,56⟩,
  ⟨55,1,0,54⟩, ⟨55,1,1,55⟩, ⟨55,1,2,56⟩,
  ⟨56,2,0,54⟩, ⟨56,2,1,55⟩, ⟨56,2,2,56⟩
]

def leftZeroCarry : Nat → Int
  | 54 => 0
  | 55 => -1
  | 56 => -2
  | _ => 0

def leftTwoCarry : Nat → Int
  | 54 => -1
  | 55 => -2
  | 56 => -3
  | _ => 0

def leftZeroEdgeOK (e : Edge) : Bool :=
  e.x - 3 * e.y + leftZeroCarry e.src = 3 * leftZeroCarry e.dst

def leftTwoEdgeOK (e : Edge) : Bool :=
  e.x - 3 * e.y + leftTwoCarry e.src = 3 * leftTwoCarry e.dst + 2

theorem left_zero_edges_exact : leftEdges.all leftZeroEdgeOK = true := by decide
theorem left_two_edges_exact : leftEdges.all leftTwoEdgeOK = true := by decide

def rightEdges : List Edge := [
  ⟨18,1,0,57⟩, ⟨18,1,1,37⟩, ⟨18,1,2,18⟩,
  ⟨19,2,0,57⟩, ⟨19,2,1,37⟩, ⟨19,2,2,18⟩,
  ⟨20,1,0,20⟩, ⟨20,1,1,57⟩, ⟨20,1,2,37⟩,
  ⟨37,2,0,37⟩, ⟨37,2,1,18⟩, ⟨37,2,2,41⟩,
  ⟨41,0,0,20⟩, ⟨41,0,1,57⟩, ⟨41,0,2,37⟩,
  ⟨57,0,0,19⟩, ⟨57,0,1,20⟩, ⟨57,0,2,57⟩
]

def rightZeroCarry : Nat → Int
  | 18 => 5
  | 19 => 1
  | 20 => 2
  | 37 => 4
  | 41 => 6
  | 57 => 3
  | _ => 0

def rightTwoCarry : Nat → Int
  | 18 => 4
  | 19 => 0
  | 20 => 1
  | 37 => 3
  | 41 => 5
  | 57 => 2
  | _ => 0

def rightZeroEdgeOK (e : Edge) : Bool :=
  4 * e.x + 3 * e.y + rightZeroCarry e.src = 3 * rightZeroCarry e.dst

def rightTwoEdgeOK (e : Edge) : Bool :=
  4 * e.x + 3 * e.y + rightTwoCarry e.src = 3 * rightTwoCarry e.dst + 2

theorem right_zero_edges_exact : rightEdges.all rightZeroEdgeOK = true := by decide
theorem right_two_edges_exact : rightEdges.all rightTwoEdgeOK = true := by decide

theorem left_sign_shift :
    [54,55,56].all (fun s => leftTwoCarry s = leftZeroCarry s - 1) = true := by decide

theorem right_sign_shift :
    [18,19,20,37,41,57].all (fun s => rightTwoCarry s = rightZeroCarry s - 1) = true := by decide

end BB6DangerousResidualSCC
