import Lean.Elab.Tactic.Omega

/-!
  Arithmetic-only right-run compatibility of the 17557 low/high action
  substitution. This module DOES NOT prove the actual six-state source
  machine executes the action words, nor that all reachable rows satisfy
  the guards. See Raw56LE17557LocalSweeps for the source triads.

  At triad boundaries, encode alternating right one/zero run lengths, with
  positive separators. For A-normal and B, the high action words ABA and BBA
  produce precisely the right run-length level map, *provided the
  terminating zero-run is not exhausted*. The case z=2 requires an explicit
  boundary-coalescence analysis; it is not covered by this lemma.
-/

namespace BB6.Agent4Raw56LE17557RightActionArithmetic

/-- Low normal-A triad produces 1² 0 1^(c+5) 0^(z-2). -/
def lowAOut (c z : Nat) : List Nat := [2, 1, c+5, z-2]

/-- High ABA triad produces 1^6 0 1^(2c+13) 0^(2z-5). -/
def highABAOut (c z : Nat) : List Nat := [6, 1, 2*c+13, 2*z-5]

/-- The fixed right-level map applied to the low normal-A output:
    first one-run 2a+2, first zero-run 2z-1, nonfinal second
    one-run 2b+3, and second zero-run 2z-1. -/
def levelLowAOut (c z : Nat) : List Nat :=
  [2*2+2, 2*1-1, 2*(c+5)+3, 2*(z-2)-1]

/-- In the non-coalescing regime, normal A → ABA respects the
    full four-run right-side level equation. -/
theorem normalA_to_ABA_right (c z : Nat) (hz : 3 ≤ z) :
    highABAOut c z = levelLowAOut c z := by
  simp [highABAOut, levelLowAOut, List.cons.injEq]
  omega

/-- Every high A/B/A triad sees the two required zeros under z≥3;
    this is the algebraic guard, not a blanket claim of source reachability. -/
theorem normalA_to_ABA_zero_guard (z : Nat) (hz : 3 ≤ z) :
    2 ≤ 2*z+1 ∧ 2 ≤ 2*z-1 ∧ 2 ≤ 2*z-3 := by
  omega

/-- Low B triad produces 1² 0 1^5 0^(a-1) 1^(b+3) 0^(z-2). -/
def lowBOut (a b z : Nat) : List Nat :=
  [2, 1, 5, a-1, b+3, z-2]

/-- High BBA triads' symbolic right-run result. -/
def highBBAOut (a b z : Nat) : List Nat :=
  [6, 1, 13, 2*a-3, 2*b+6, 2*z-3]

/-- Fixed right-level map on the six alternating low B output runs.
    The third one-run is nonfinal and the third zero-run is later. -/
def levelLowBOut (a b z : Nat) : List Nat :=
  [2*2+2, 2*1-1, 2*5+3, 2*(a-1)-1,
    2*(b+3), 2*(z-2)+1]

/-- In the non-coalescing regime, B → BBA respects the
    entire six-run right-level map. -/
theorem B_to_BBA_right (a b z : Nat)
    (ha : 2 ≤ a) (hz : 3 ≤ z) :
    highBBAOut a b z = levelLowBOut a b z := by
  simp [highBBAOut, levelLowBOut, List.cons.injEq]
  omega

/-- Every component of the BBA sweep's zero obligations is long enough.
    The action B itself requires a≥2 and z≥2; z≥3 is what keeps the final
    residual zero-run positive for level conjugacy. -/
theorem B_to_BBA_zero_guard (a z : Nat)
    (ha : 2 ≤ a) (hz : 3 ≤ z) :
    2 ≤ 2*z-1 ∧ 2 ≤ 2*a+1 ∧ 2 ≤ 2*a-1 ∧ 1 ≤ z-2 := by
  omega

/-- The z=2 boundary does not satisfy the non-coalescing high ABA
    intermediate guard: its third high triad sees only one trailing zero. -/
theorem normalA_z2_boundary :
    2*2-3 = 1 ∧ ¬ (2 ≤ 2*2-3) := by decide

/-- The z=2 low output has no trailing zero-run, whereas the high BBA
    right output retains exactly one trailing zero. Hence the six-run
    interpretation cannot be naively extended across coalescing tails. -/
theorem B_z2_boundary (a b : Nat) :
    (lowBOut a b 2).getLast? = some 0 ∧
    (highBBAOut a b 2).getLast? = some 1 := by
  simp [lowBOut,highBBAOut]

#print axioms normalA_to_ABA_right
#print axioms normalA_to_ABA_zero_guard
#print axioms B_to_BBA_right
#print axioms B_to_BBA_zero_guard
#print axioms normalA_z2_boundary
#print axioms B_z2_boundary

end BB6.Agent4Raw56LE17557RightActionArithmetic
