import BB6Coverage
import Raw122RootCompose
import Raw122SharpWitnesses
import Raw122Recovered14
import Raw122Recovered04
import Raw122Recovered12
import Raw122Recovered13
import Raw122RecoveredLC
import Raw122Recovered18
import Raw122Recovered23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent43Raw122SharpParent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath

private theorem lift7014 {m : Machine}
    (h : WeightedBound 7014 m) : WeightedBound 6659487 m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) (by decide)

theorem child_covers (mv : Move) (m : Machine)
    (hm : compatible (BB6.Agent43Raw122.child mv) m) :
    WeightedBound 6659487 m := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact lift7014 (BB6.Agent43Raw122Sharp.cover00 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover06 m hm)
  · exact lift7014 (BB6.Agent3Raw122Recovered12.cover12 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered18.cover18 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover01 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover07 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered13.cover13 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover19 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover02 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover08 m hm)
  · exact lift7014 (BB6.Agent43Raw122RecoveredLC.cover14 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover20 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover03 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover09 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover15 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover21 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered04.cover04 m hm)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover10 m hm)
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent43Raw122Sharp.cover16 m hm k d hk hd) (by decide)
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover22 m hm)
  · exact BB6.Agent43Raw122Sharp.cover05 m hm
  · exact lift7014 (BB6.Agent43Raw122Recovered14.cover11 m hm)
  · exact lift7014 (BB6.Agent43Raw122Sharp.cover17 m hm)
  · exact lift7014 (BB6.Agent3Raw122Recovered23.cover23 m hm)

theorem parent_bound (m : Machine)
    (hm : compatible BB6.Agent43Raw122.parent m) :
    WeightedBound 6659487 m := by
  exact BB6.Agent43Raw122RootCompose.root_bound 6659487 (by decide)
    child_covers m hm

theorem exact_bound_iff (B : Nat) :
    (∀ m, compatible BB6.Agent43Raw122.parent m → WeightedBound B m) ↔ 6659487 ≤ B := by
  constructor
  · exact BB6.Agent43Raw122Sharp.lower B
  · intro h m hm k d hk hd
    exact Nat.le_trans (parent_bound m hm k d hk hd) h

#print axioms exact_bound_iff
#print axioms child_covers
#print axioms parent_bound
end BB6.Agent43Raw122SharpParent
