import Std
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SheepRootGateDensity

abbrev Gate4 (m : Nat) : Prop :=
  m % 3 ≠ 0 ∧ m % 4 = 0 ∧ m % 7 ≠ 2 ∧ m % 9 ≠ 8 ∧ m % 15 ≠ 7

abbrev Gate5 (m : Nat) : Prop :=
  m % 3 ≠ 0 ∧ m % 4 = 0 ∧ m % 7 ≠ 3 ∧ m % 9 ≠ 4 ∧ m % 15 ≠ 11

/-- All h4 gate indices lie on the 216-divisible exponent spine. -/
theorem gate4_216 (m : Nat) (h : Gate4 m) : (54*m) % 216 = 0 := by
  rcases h with ⟨_, h4, _, _, _⟩
  omega

/-- All h5 gate indices lie on the same 216-divisible spine. -/
theorem gate5_216 (m : Nat) (h : Gate5 m) : (162*m) % 216 = 0 := by
  rcases h with ⟨_, h4, _, _, _⟩
  omega

/-- The original 648+122472*k E family always retains a fifth-layer a=2 parent. -/
theorem old648_outside_gate5 (k : Nat) : ¬ Gate5 (4+756*k) := by
  intro h
  rcases h with ⟨_, _, _, h9, _⟩
  have hh : (4+756*k) % 9 = 4 := by omega
  exact h9 hh

/-- Strict period-count statements, kernel-checked rather than relying on a Python census. -/
theorem exact_count4 :
    ((List.range 1260).filter (fun m => decide (Gate4 m))).length = 132 := by
  decide

theorem exact_count5 :
    ((List.range 1260).filter (fun m => decide (Gate5 m))).length = 132 := by
  decide

/-- These are explicit unbounded source-index families, without any finite cutoff. -/
theorem family4 (k : Nat) : Gate4 (4 + 1260*k) := by
  unfold Gate4
  omega

theorem family5 (k : Nat) : Gate5 (8 + 1260*k) := by
  unfold Gate5
  omega

/-- The arithmetic restrictions eliminate all h<=4 parent-sector congruences. -/
theorem all_branches4_false (m : Nat) (h : Gate4 m) :
    ¬ (m % 2 = 1 ∨ m % 4 = 2 ∨ m % 7 = 2 ∨ m % 9 = 8 ∨ m % 15 = 7) := by
  rcases h with ⟨_, h4, h7, h9, h15⟩
  omega

/-- The arithmetic restrictions eliminate all h<=5 parent-sector congruences. -/
theorem all_branches5_false (m : Nat) (h : Gate5 m) :
    ¬ (m % 2 = 1 ∨ m % 4 = 2 ∨ m % 7 = 3 ∨ m % 9 = 4 ∨ m % 15 = 11) := by
  rcases h with ⟨_, h4, h7, h9, h15⟩
  omega

#print axioms exact_count4
#print axioms exact_count5
#print axioms gate4_216
#print axioms gate5_216
#print axioms old648_outside_gate5
#print axioms family4
#print axioms family5
#print axioms all_branches4_false
#print axioms all_branches5_false
end SheepRootGateDensity
