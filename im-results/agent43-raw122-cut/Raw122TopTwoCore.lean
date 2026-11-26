import Raw122ExceptionalLeaves
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122TopTwoCore
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122Sharp BB6.Agent43Raw122Exceptional
open BB6.Agent43Raw122 (parent_root parent_nohalt)

/-- The exact pointwise exception-preserving child interface. -/
def ChildExcept : Prop := ∀ (m : Machine), m ≠ longest → m ≠ second →
    ∀ (mv : Move), compatible (BB6.Agent43Raw122.child mv) m → WeightedBound 7014 m

theorem parent_except (small : ChildExcept) (m : Machine) (hm : compatible BB6.Agent43Raw122.parent m)
    (hne0 : m ≠ longest) (hne1 : m ≠ second) : WeightedBound 7014 m := by
  let t : PartialAudit := .split 7 (5,true) (fun _ => .unresolved)
  have hcheck : partialCheck 7014 BB6.Agent43Raw122.parent t = true := by
    rw [partialCheck.eq_3,Bool.and_eq_true]
    exact ⟨by decide,allMoves_of _ (by intro mv; rfl)⟩
  rcases partialSound 7014 BB6.Agent43Raw122.parent t BB6.Agent43Raw122.parent_root
      BB6.Agent43Raw122.parent_nohalt hcheck m hm with h|⟨e,he,hh⟩
  · exact h
  · rw [partialResiduals.eq_3] at he
    obtain ⟨mv,_,hmem⟩ := List.mem_flatMap.mp he
    rw [partialResiduals.eq_1] at hmem
    obtain ⟨e',he',heq⟩ := List.mem_map.mp hmem
    have he'' : e' = ([], BB6.Agent43Raw122.child mv) := by
      simpa only [List.mem_singleton] using he'
    rw [← heq,he''] at hh
    exact small m hne0 hne1 mv hh

theorem runner_up_bound (small : ChildExcept) (m : Machine) (hm : compatible BB6.Agent43Raw122.parent m)
    (hne : m ≠ longest) : WeightedBound 1296926 m := by
  by_cases h : m = second
  · subst m
    exact late1_bound second second_compatible
  · intro k d hk hd
    exact Nat.le_trans (parent_except small m hm hne h k d hk hd) (by decide)

theorem runner_up_exact (small : ChildExcept) (B : Nat) :
    (∀ m, compatible BB6.Agent43Raw122.parent m → m ≠ longest → WeightedBound B m) ↔ 1296926 ≤ B := by
  constructor
  · intro h
    exact h second second_parent_compatible second_ne_longest 1296924 1 second_halts second_delay
  · intro h m hm hne k d hk hd
    exact Nat.le_trans (runner_up_bound small m hm hne k d hk hd) h

theorem parent_bound (small : ChildExcept) (m : Machine)
    (hm : compatible BB6.Agent43Raw122.parent m) : WeightedBound 6659487 m := by
  by_cases h : m = longest
  · subst m
    exact late0_bound longest longest_compatible
  · intro k d hk hd
    exact Nat.le_trans (runner_up_bound small m hm h k d hk hd) (by decide)

theorem exact_bound_iff (small : ChildExcept) (B : Nat) :
    (∀ m, compatible BB6.Agent43Raw122.parent m → WeightedBound B m) ↔ 6659487 ≤ B := by
  constructor
  · exact lower B
  · intro h m hm k d hk hd
    exact Nat.le_trans (parent_bound small m hm k d hk hd) h

#print axioms parent_except
#print axioms runner_up_exact
#print axioms exact_bound_iff
end BB6.Agent43Raw122TopTwoCore
