import Raw122SharpParent
import Raw122ExceptionalBranches
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

/-- No completion other than the two exact late-query halters has
weighted halting score greater than the original 7014 audit cutoff. -/
theorem parent_except (m : Machine) (hm : compatible BB6.Agent43Raw122.parent m)
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
    exact child_except m hne0 hne1 mv hh

theorem runner_up_bound (m : Machine) (hm : compatible BB6.Agent43Raw122.parent m)
    (hne : m ≠ longest) : WeightedBound 1296926 m := by
  by_cases h : m = second
  · subst m
    exact late1_bound second second_compatible
  · intro k d hk hd
    exact Nat.le_trans (parent_except m hm hne h k d hk hd) (by decide)

theorem runner_up_exact (B : Nat) :
    (∀ m, compatible BB6.Agent43Raw122.parent m → m ≠ longest → WeightedBound B m) ↔
      1296926 ≤ B := by
  constructor
  · intro h
    exact h second second_parent_compatible second_ne_longest 1296924 1 second_halts second_delay
  · intro h m hm hne k d hk hd
    exact Nat.le_trans (runner_up_bound m hm hne k d hk hd) h

#print axioms parent_except
#print axioms runner_up_bound
#print axioms runner_up_exact
end BB6.Agent43Raw122TopTwo
