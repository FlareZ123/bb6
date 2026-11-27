import Raw61Data

namespace BB6.Agent31Raw61
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent10Raw61

/-- Exact seven assigned cells of the retained Raw61 parent. -/
def literalParent : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem parent_eq_literal : p61 = literalParent := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

theorem parent_cover : Cover (WeightedBound 1962) p61 := Cover.leaf p61 all61

theorem literal_cover : Cover (WeightedBound 1962) literalParent := by
  rw [← parent_eq_literal]
  exact parent_cover

#print axioms parent_eq_literal
#print axioms parent_cover
#print axioms literal_cover
end BB6.Agent31Raw61
