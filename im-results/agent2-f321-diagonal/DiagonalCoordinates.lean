import SourceCounter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321Diagonal
open BB6.Agent31F321Density

def X (a d : Nat) : Nat := a + d + 5
def Y (d : Nat) : Nat := 2 * (d + 3)
def Z (a d : Nat) : Int := (Y d : Int) - (X a d : Int)

theorem terminal_iff_diagonal (a d : Nat) : X a d = Y d ↔ a = d + 1 := by
  unfold X Y
  omega

theorem high_guard_iff (a d : Nat) : d + 2 ≤ a ↔ Y d < X a d := by
  unfold X Y
  omega

theorem equal_guard_iff (a d : Nat) : a = d ↔ X a d + 1 = Y d := by
  unfold X Y
  omega

theorem below_guard_iff (a d : Nat) : a < d ↔ X a d + 2 ≤ Y d := by
  unfold X Y
  omega

theorem far_guard_iff (a d : Nat) (h : a < d) :
    3 * a + 1 ≤ d ↔ 3 * X a d ≤ 2 * Y d + 2 := by
  unfold X Y
  omega

theorem middle_guard_iff (a d : Nat) (h : a < d) :
    d < 3 * a + 1 ↔ 2 * Y d + 2 < 3 * X a d := by
  unfold X Y
  omega

theorem middle_even_parity (a d : Nat) (h : a < d) :
    (d - a) % 2 = 0 ↔ X a d % 2 = 1 := by
  unfold X
  omega

theorem middle_odd_parity (a d : Nat) (h : a < d) :
    (d - a) % 2 = 1 ↔ X a d % 2 = 0 := by
  unfold X
  omega

theorem high_coordinates (a d : Nat) (h : d + 2 ≤ a) :
    X (a-d-2) (2*d+3) = X a d + 1 ∧
    Y (2*d+3) = 2 * Y d := by
  unfold X Y
  omega

theorem equal_coordinates (a : Nat) :
    X (2*a+4) 1 = X a a + 5 ∧ Y 1 = 8 := by
  unfold X Y
  omega

theorem far_coordinates (a d : Nat) (h1 : a < d) (h2 : 3*a+1 ≤ d) :
    X (4*a+6) (d-3*a) = X a d + 6 ∧
    Y (d-3*a) = 4 * Y d + 12 - 6 * X a d := by
  unfold X Y
  omega

theorem middle_even_coordinates (a d : Nat) (h1 : a < d)
    (h2 : d < 3*a+1) (hp : (d-a)%2=0) :
    X (4*a+6) 2 = 2 * X a d + 5 - 2 * (Y d - X a d) ∧
    Y 2 = 10 ∧ X (4*a+6) 2 % 4 = 1 := by
  unfold X Y
  constructor
  · omega
  constructor
  · decide
  · omega

theorem middle_odd_coordinates (a d : Nat) (h1 : a < d)
    (h2 : d < 3*a+1) (hp : (d-a)%2=1) :
    X (4*a+6) 1 = 2 * X a d + 4 - 2 * (Y d - X a d) ∧
    Y 1 = 8 ∧ X (4*a+6) 1 % 4 = 0 := by
  unfold X Y
  constructor
  · omega
  constructor
  · decide
  · omega

/-- Exact source moves transported into diagonal coordinates. -/
theorem move_coordinate_cases {a d A D : Nat} (h : CounterMove a d A D) :
    (Y d < X a d ∧ X A D = X a d + 1 ∧ Y D = 2 * Y d) ∨
    (X a d + 1 = Y d ∧ X A D = X a d + 5 ∧ Y D = 8) ∨
    (X a d + 2 ≤ Y d ∧ 3 * X a d ≤ 2 * Y d + 2 ∧
      X A D = X a d + 6 ∧ Y D = 4 * Y d + 12 - 6 * X a d) ∨
    (X a d + 2 ≤ Y d ∧ 2 * Y d + 2 < 3 * X a d ∧ X a d % 2 = 1 ∧
      Y D = 10 ∧ X A D % 4 = 1) ∨
    (X a d + 2 ≤ Y d ∧ 2 * Y d + 2 < 3 * X a d ∧ X a d % 2 = 0 ∧
      Y D = 8 ∧ X A D % 4 = 0) := by
  cases h with
  | high d hg =>
      left
      have hg' := (high_guard_iff _ _).mp hg
      have hc := high_coordinates _ _ hg
      exact ⟨hg', hc.1, hc.2⟩
  | equal =>
      right; left
      exact ⟨(equal_guard_iff a a).mp rfl, (equal_coordinates a).1,
        (equal_coordinates a).2⟩
  | far d h1 h2 =>
      right; right; left
      have hb := (below_guard_iff _ _).mp h1
      have hf := (far_guard_iff _ _ h1).mp h2
      have hc := far_coordinates _ _ h1 h2
      exact ⟨hb,hf,hc.1,hc.2⟩
  | middleEven d h1 h2 hp =>
      right; right; right; left
      have hb := (below_guard_iff _ _).mp h1
      have hm := (middle_guard_iff _ _ h1).mp h2
      have hp' := (middle_even_parity _ _ h1).mp hp
      have hc := middle_even_coordinates _ _ h1 h2 hp
      exact ⟨hb,hm,hp',hc.2.1,hc.2.2⟩
  | middleOdd d h1 h2 hp =>
      right; right; right; right
      have hb := (below_guard_iff _ _).mp h1
      have hm := (middle_guard_iff _ _ h1).mp h2
      have hp' := (middle_odd_parity _ _ h1).mp hp
      have hc := middle_odd_coordinates _ _ h1 h2 hp
      exact ⟨hb,hm,hp',hc.2.1,hc.2.2⟩

#print axioms terminal_iff_diagonal
#print axioms move_coordinate_cases
end BB6.Agent2F321Diagonal
