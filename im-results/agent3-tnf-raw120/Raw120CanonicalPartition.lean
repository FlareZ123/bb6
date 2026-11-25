import FrontierMass
import Raw120RFData
import Raw120RBData
import Canonical78Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120Partition
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent3Raw120 BB6.Agent3Raw120RB
open BB6.Agent10ZipAudit BB6.Agent31ThreeHole

abbrev hole : Slot := (4,false)
abbrev rfChoice : Transition := some ⟨false,true,5⟩
abbrev rbChoice : Transition := some ⟨false,true,1⟩

theorem immediate_halt_checked : zipQueryOK 15 p120 9 hole = true := by decide

/-- All completions of the immediate-halt child satisfy the bound, including
    the possible zero-write prefix and the final halting query. -/
theorem immediate_halt_bound :
    ∀ m, compatible (refine p120 hole none) m → WeightedBound 15 m := by
  obtain ⟨hr,hh,hw⟩ := zipQueryOK_sound immediate_halt_checked
  cases hrun : knownRun p120 9 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = hole := by simpa [hrun] using hr
    have h := first_hole_weighted_halt 15 p120 9 c (by decide) hrun
      (by simpa [hs] using hh)
      (by simpa [hs] using weightOK_sound p120 hole 9 15 hw)
    simpa [hs] using h

def remaining : List Transition :=
  choices.filter (fun t => decide (t ≠ none ∧ t ≠ rfChoice ∧ t ≠ rbChoice))

theorem remaining_count : remaining.length = 22 := by decide

theorem remaining_mass :
    ((remaining.map (fun t => cylinderMass (refine p120 hole t))).sum) =
      22 * 25^5 := by decide

theorem partition_sound (B : Nat) (hB : 14416 ≤ B)
    (m : Machine) (hm : compatible p120 m) :
    WeightedBound B m ∨
      ∃ t ∈ remaining, compatible (refine p120 hole t) m := by
  have hc := compatible_refine p120 m hole hm
  by_cases h0 : m hole = none
  · left
    have h := immediate_halt_bound m (by simpa [h0] using hc)
    intro k d hk hd
    exact Nat.le_trans (h k d hk hd) (by omega)
  by_cases hRF : m hole = rfChoice
  · left
    have h := allRF m (by simpa [hRF, pRF] using hc)
    intro k d hk hd
    exact Nat.le_trans (h k d hk hd) hB
  by_cases hRB : m hole = rbChoice
  · left
    have h := allRB m (by simpa [hRB, pRB] using hc)
    intro k d hk hd
    exact Nat.le_trans (h k d hk hd) (by omega)
  · right
    refine ⟨m hole, List.mem_filter.mpr ⟨choices_complete _, ?_⟩, hc⟩
    simp [h0,hRF,hRB]

theorem cover_from_remaining (B : Nat) (hB : 14416 ≤ B)
    (hLeaves : ∀ t ∈ remaining, Cover (WeightedBound B) (refine p120 hole t)) :
    Cover (WeightedBound B) p120 := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases partition_sound B hB m hm with hb | ⟨t, ht, hc⟩
  · exact hb
  · exact (hLeaves t ht).sound m hc

def raw120Address : List Move :=
  [⟨true,true,2⟩, ⟨false,true,3⟩, ⟨true,false,3⟩,
   ⟨true,true,4⟩, ⟨true,false,4⟩]

theorem raw120_mem_canonical78 :
    (raw120Address,p120) ∈ BB6.Agent47Canonical78.roster := by decide

/-- Consume the entire raw120 parent partition in the mixed-bound quotient
    interface. No sibling is silently removed, and the other roster
    obligations remain explicit. -/
theorem exact_from_raw120_partition (B : Nat) (hB : 14416 ≤ B)
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ p120 → Cover (WeightedBound B) e.2)
    (hLeaves : ∀ t ∈ remaining, Cover (WeightedBound B) (refine p120 hole t))
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent47Canonical78.exact_at_target B (by omega)
    (by
      intro e he
      by_cases hEq : e.2 = p120
      · simpa [hEq] using cover_from_remaining B hB hLeaves
      · exact hOther e he hEq)
    champ

#print axioms immediate_halt_bound
#print axioms remaining_count
#print axioms remaining_mass
#print axioms partition_sound
#print axioms cover_from_remaining
#print axioms raw120_mem_canonical78
#print axioms exact_from_raw120_partition

end BB6.Agent3Raw120Partition
