import Q2800Trees
import Raw10BoxCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Q2800
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge BB6.Agent49Box
open BB6.Agent13CrossRouteHeldLeaf109

/-- Retain the previous disjoint rectangles with one shared exclusion predicate. -/
def factoredRemainder (p : PartialMachine) (previous : List PartialMachine) (m : Machine) : Prop :=
  (∃ r ∈ remainder p previous, Fits r m) ∧ uncovered m

theorem factored_exact (p : PartialMachine) (previous : List PartialMachine) (m : Machine) :
    factoredRemainder p previous m ↔ ∃ r ∈ remainder p (previous ++ tables), Fits r m := by
  unfold factoredRemainder uncovered
  rw [remainder_exact, remainder_exact]
  constructor
  · rintro ⟨⟨hp,hprev⟩,hnew⟩
    exact ⟨hp, fun q hq => (List.mem_append.mp hq).elim (hprev q) (hnew q)⟩
  · rintro ⟨hp,hall⟩
    exact ⟨⟨hp,fun q hq => hall q (List.mem_append.mpr (Or.inl hq))⟩,
      fun q hq => hall q (List.mem_append.mpr (Or.inr hq))⟩

theorem tables_refine_parent_checked :
    roster.all (fun e => refinesMachineB e.table firstOneB0_1LC) = true := by decide

def raw10_cover_q2800 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ m, factoredRemainder firstOneB0_1LC (sideTables ++ [held]) m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  raw10_cover B hB hHeld (fun r hr m hm =>
    (safe_or_uncovered B (Nat.le_trans (by decide : 400 ≤ 7014) hB) m).elim id
      (fun hno => hOpen m ⟨⟨r,hr,hm⟩,hno⟩))
#print axioms factored_exact
#print axioms tables_refine_parent_checked
#print axioms raw10_cover_q2800
end BB6.Agent50Q2800
