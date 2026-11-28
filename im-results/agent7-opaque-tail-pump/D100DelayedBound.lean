import D100DelayedTrace
import Run0LastHole
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7D100DelayedBound
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent7D100Delayed

theorem rest : ∀ s : Slot, s ≠ (final.q,final.l.headD false) → ∃ mv, table s = some (some mv) := by
  intro s hs
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b
  all_goals first | (exact False.elim (hs rfl)) | (exact ⟨_,rfl⟩)

theorem bound (m : Machine) (hm : compatible table m) : WeightedBound 53257978073992281 m :=
  BB6.Agent7Run0LastHole.bound table 53257978073992275 53257978073992281 final reached rfl rest (by decide) m hm

#print axioms bound
end BB6.Agent7D100DelayedBound
