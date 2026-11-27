import Raw57ParentComplete

namespace BB6.Agent31Raw57
open BB6Coverage BB6.Agent13BlankDelay
def literalParent : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem parent_eq_literal : BB6.Agent1Raw57Parent.parent = literalParent := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

theorem literal_cover : Cover (WeightedBound 1613) literalParent := by
  rw [← parent_eq_literal]
  exact BB6.Agent1Raw57Complete.parent_cover

#print axioms parent_eq_literal
#print axioms literal_cover
end BB6.Agent31Raw57
