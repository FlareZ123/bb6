import Raw56LBE11LBReduced
import M21049
import M3923Pair
import M39234
import M39233
import M39232Min
import M42763Final
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw56LB.E11LB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

private theorem match21049 : table21049 = BB6.Agent4Raw56RootE11LB.M21049.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

private theorem safe21049 (m : Machine) (hm : compatible table21049 m) :
    WeightedBound 1000000 m := by
  apply weighted_never 1000000 m
  exact BB6.Agent4Raw56RootE11LB.M21049.never m (by simpa only [match21049] using hm)

private theorem match39232 : table39232 = BB6.Agent4Raw56RootE11LB.M39232Block.M39232.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

private theorem safe39232 (m : Machine) (hm : compatible table39232 m) :
    WeightedBound 1000000 m := by
  apply weighted_never 1000000 m
  exact BB6.Agent4Raw56RootE11LB.M39232Block.M39232.never m (by simpa only [match39232] using hm)

private theorem match39233 : table39233 = BB6.Agent4Raw56RootE11LB.M39233.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

private theorem safe39233 (m : Machine) (hm : compatible table39233 m) :
    WeightedBound 1000000 m := by
  apply weighted_never 1000000 m
  exact BB6.Agent4Raw56RootE11LB.M39233.never m (by simpa only [match39233] using hm)

private theorem match39234 : table39234 = BB6.Agent4Raw56RootE11LB.M39234.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

private theorem safe39234 (m : Machine) (hm : compatible table39234 m) :
    WeightedBound 1000000 m := by
  apply weighted_never 1000000 m
  exact BB6.Agent4Raw56RootE11LB.M39234.never m (by simpa only [match39234] using hm)

private theorem match42763 : table42763 = BB6.Agent4Raw56RootE11LB.M42763Block.M42763.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

private theorem safe42763 (m : Machine) (hm : compatible table42763 m) :
    WeightedBound 1000000 m := by
  apply weighted_never 1000000 m
  exact BB6.Agent4Raw56RootE11LB.M42763Block.M42763.never m (by simpa only [match42763] using hm)

/-- Source proof of complete reduction of the E1=1LB six-hole sibling to
    exactly one unresolved literal one-hole residual M23706 (not a Cover). -/
theorem all_except_23706 (m : Machine) (hm : TNFQuotientCompatible p m) :
    WeightedBound 1000000 m ∨ compatible table23706 m := by
  rcases reduced_quotient m hm with hb | ⟨q,hq,hc⟩
  · exact Or.inl hb
  · simp only [hardTables,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with h|h|h|h|h|h
    · subst q
      exact Or.inl (quotientSafe (by decide) safe21049 m hc)
    · subst q
      exact Or.inr hc
    · subst q
      exact Or.inl (quotientSafe (by decide) safe39232 m hc)
    · subst q
      exact Or.inl (quotientSafe (by decide) safe39233 m hc)
    · subst q
      exact Or.inl (quotientSafe (by decide) safe39234 m hc)
    · subst q
      exact Or.inl (quotientSafe (by decide) safe42763 m hc)

#print axioms all_except_23706
end BB6.Agent4Raw56LB.E11LB
