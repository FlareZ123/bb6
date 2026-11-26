import Raw122TopTwoCore
import Raw122Sharp00
import Raw122Sharp17
import Raw122ExceptionalBranches
import Raw122Recovered14
import Raw122Recovered04
import Raw122Recovered12
import Raw122Recovered13
import Raw122RecoveredLC
import Raw122Recovered18
import Raw122Recovered23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122TopTwo
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122Sharp BB6.Agent43Raw122Exceptional

theorem child_except (m : Machine) (hne0 : m ≠ longest) (hne1 : m ≠ second)
    (mv : Move) (hm : compatible (BB6.Agent43Raw122.child mv) m) :
    WeightedBound 7014 m := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact BB6.Agent43Raw122Sharp.cover00 m hm
  · exact BB6.Agent43Raw122Recovered14.cover06 m hm
  · exact BB6.Agent3Raw122Recovered12.cover12 m hm
  · exact BB6.Agent43Raw122Recovered18.cover18 m hm
  · exact BB6.Agent43Raw122Recovered14.cover01 m hm
  · exact BB6.Agent43Raw122Recovered14.cover07 m hm
  · exact BB6.Agent43Raw122Recovered13.cover13 m hm
  · exact BB6.Agent43Raw122Recovered14.cover19 m hm
  · exact BB6.Agent43Raw122Recovered14.cover02 m hm
  · exact BB6.Agent43Raw122Recovered14.cover08 m hm
  · exact BB6.Agent43Raw122RecoveredLC.cover14 m hm
  · exact BB6.Agent43Raw122Recovered14.cover20 m hm
  · exact BB6.Agent43Raw122Recovered14.cover03 m hm
  · exact BB6.Agent43Raw122Recovered14.cover09 m hm
  · exact BB6.Agent43Raw122Recovered14.cover15 m hm
  · exact BB6.Agent43Raw122Recovered14.cover21 m hm
  · exact BB6.Agent43Raw122Recovered04.cover04 m hm
  · exact BB6.Agent43Raw122Recovered14.cover10 m hm
  · exact BB6.Agent43Raw122Roster.cover16_except m hm hne1
  · exact BB6.Agent43Raw122Recovered14.cover22 m hm
  · exact BB6.Agent43Raw122Roster.cover05_except m hm hne0
  · exact BB6.Agent43Raw122Recovered14.cover11 m hm
  · exact BB6.Agent43Raw122Sharp.cover17 m hm
  · exact BB6.Agent3Raw122Recovered23.cover23 m hm

theorem all_children : BB6.Agent43Raw122TopTwoCore.ChildExcept := child_except

theorem parent_except := BB6.Agent43Raw122TopTwoCore.parent_except all_children

theorem runner_up_bound := BB6.Agent43Raw122TopTwoCore.runner_up_bound all_children

theorem runner_up_exact := BB6.Agent43Raw122TopTwoCore.runner_up_exact all_children

theorem parent_bound := BB6.Agent43Raw122TopTwoCore.parent_bound all_children

theorem exact_bound_iff := BB6.Agent43Raw122TopTwoCore.exact_bound_iff all_children

#print axioms parent_except
#print axioms runner_up_exact
#print axioms exact_bound_iff
end BB6.Agent43Raw122TopTwo
