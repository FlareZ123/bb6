import Q2800Trees1
import Q2800Trees2
import Q2800Trees3
import Q2800Trees4
import Q2800Trees5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Q2800
open BB6Coverage BB6.Agent13BlankDelay
def roster : List ClosedTree := chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5
def tables : List PartialMachine := roster.map ClosedTree.table
theorem roster_length : roster.length = 95 := by decide
theorem tables_safe (B : Nat) (hB : 400 ≤ B) :
    ∀ q ∈ tables, ∀ m, compatible q m → WeightedBound B m := by
  intro q hq m hm
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hq
  have h := e.sound m hm
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hB
def uncovered (m : Machine) : Prop :=
  ∀ q ∈ tables, ¬ compatible q m
theorem safe_or_uncovered (B : Nat) (hB : 400 ≤ B) (m : Machine) :
    WeightedBound B m ∨ uncovered m := by
  classical
  by_cases h : ∃ q ∈ tables, compatible q m
  · obtain ⟨q,hq,hm⟩ := h
    exact Or.inl (tables_safe B hB q hq m hm)
  · exact Or.inr (fun q hq hm => h ⟨q,hq,hm⟩)
#print axioms tables_safe
#print axioms safe_or_uncovered
end BB6.Agent50Q2800
