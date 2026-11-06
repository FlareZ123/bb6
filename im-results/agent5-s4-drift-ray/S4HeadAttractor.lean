import S4ToggleHead
import Lean.Elab.Tactic.Omega

namespace S4HeadAttractor
open S4ToggleHead
set_option maxHeartbeats 0

/-- Heads below the absorbing band move strictly toward it. -/
theorem low_move (a : Nat) (ha : a<280) : a < f a ∧ f a ≤ 284 := by
  dsimp [f,h]
  split <;> split <;> split <;> omega

/-- Heads above the absorbing band move strictly toward it. -/
theorem high_move (a : Nat) (ha : 284 < a) : 280 ≤ f a ∧ f a < a := by
  dsimp [f,h]
  split <;> split <;> split <;> omega

theorem band_cycle (a : Nat) (ha : 280 ≤ a) (hb : a ≤ 284) :
    280 ≤ f a ∧ f a ≤ 284 := by
  rcases (show a=280 ∨ a=281 ∨ a=282 ∨ a=283 ∨ a=284 by omega) with h|h|h|h|h
  all_goals subst a <;> decide

def delta (a : Nat) : Nat := (280-a)+(a-284)

theorem delta_zero (a : Nat) : delta a = 0 ↔ 280 ≤ a ∧ a ≤284 := by
  unfold delta
  omega

theorem delta_decreases (a : Nat) : delta (f a) ≤ delta a - 1 := by
  by_cases hl : a<280
  · obtain ⟨hal,har⟩ := low_move a hl
    unfold delta
    omega
  · by_cases hh : 284<a
    · obtain ⟨hal,har⟩ := high_move a hh
      unfold delta
      omega
    · have hband : 280≤a ∧ a≤284 := by omega
      obtain ⟨hal,har⟩ := band_cycle a hband.1 hband.2
      unfold delta
      omega

def hrun : Nat → Nat → Nat
  | 0,a => a
  | n+1,a => f (hrun n a)

theorem delta_bound (n a : Nat) : delta (hrun n a) ≤ delta a - n := by
  induction n with
  | zero => simp [hrun]
  | succ n ih =>
      change delta (f (hrun n a)) ≤ delta a - (n+1)
      have hs := delta_decreases (hrun n a)
      omega

/-- Every arbitrary natural-number head enters the absorbing band in no more
    than delta(a) returns, as a theorem of the total head projection. -/
theorem eventually_band (a : Nat) :
    280 ≤ hrun (delta a) a ∧ hrun (delta a) a ≤284 := by
  have hb := delta_bound (delta a) a
  apply (delta_zero _).mp
  omega

theorem dynamics_on_band :
    f 280=281 ∧ f 281=283 ∧ f 283=282 ∧ f 282=280 ∧ f 284=284 := by
  decide

#print axioms low_move
#print axioms high_move
#print axioms band_cycle
#print axioms delta_decreases
#print axioms delta_bound
#print axioms eventually_band
#print axioms dynamics_on_band
end S4HeadAttractor
