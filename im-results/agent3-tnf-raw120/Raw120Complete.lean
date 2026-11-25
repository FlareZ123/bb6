import Raw120EasyCycles
import Raw120LAData
import Raw120ZeroLBData
import Raw120ZeroLFData
import Raw120RAData
import Raw120RBData
import Raw120RCData
import Raw120RFData
import Raw120OneLAData
import Raw120OneLBData
import Raw120OneLFData
import Raw120OneRAData
import Raw120OneRBData
import Raw120OneRCData
import Raw120OneRFData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120Complete
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent3Raw120
open BB6.Agent10ZipAudit BB6.Agent31ThreeHole

abbrev hole : Slot := (4,false)

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


private theorem widen {a b : Nat} {m : Machine}
    (h : WeightedBound a m) (hab : a ≤ b) : WeightedBound b m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hab

private def noncycleChoices : List Transition :=
  [none, some ⟨false,false,0⟩, some ⟨false,false,1⟩, some ⟨false,false,5⟩, some ⟨false,true,0⟩, some ⟨false,true,1⟩, some ⟨false,true,2⟩, some ⟨false,true,5⟩, some ⟨true,false,0⟩, some ⟨true,false,1⟩, some ⟨true,false,5⟩, some ⟨true,true,0⟩, some ⟨true,true,1⟩, some ⟨true,true,2⟩, some ⟨true,true,5⟩]

private theorem choices_partition :
    (choices.filter (fun t => decide (t ∉ BB6.Agent3Raw120EasyCycles.cycleChoices))).all
      (fun t => decide (t ∈ noncycleChoices)) = true := by decide

/-- Direct parent proof. All 25 alternatives have an explicit source certificate.
    This declaration is accepted only after all imported child modules compile. -/
theorem allChildren (t : Transition) (ht : t ∈ choices) (m : Machine)
    (hm : compatible (refine p120 hole t) m) : WeightedBound 224707 m := by
  by_cases hc : t ∈ BB6.Agent3Raw120EasyCycles.cycleChoices
  · exact widen (BB6.Agent3Raw120EasyCycles.cycles_sound t hc m hm) (by decide)
  have hf : t ∈ choices.filter (fun u => decide (u ∉ BB6.Agent3Raw120EasyCycles.cycleChoices)) :=
    List.mem_filter.mpr ⟨ht, by simpa using hc⟩
  have hn : t ∈ noncycleChoices := of_decide_eq_true (List.all_eq_true.mp choices_partition t hf)
  simp only [noncycleChoices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
  all_goals subst t
  · exact widen (immediate_halt_bound m hm) (by decide)
  · exact widen (BB6.Agent3Raw120LA.allLA m hm) (by decide)
  · exact widen (BB6.Agent3Raw120ZeroLB.allZeroLB m hm) (by decide)
  · exact widen (BB6.Agent3Raw120ZeroLF.allZeroLF m hm) (by decide)
  · exact widen (BB6.Agent3Raw120RA.allRA m hm) (by decide)
  · exact widen (BB6.Agent3Raw120RB.allRB m hm) (by decide)
  · exact widen (BB6.Agent3Raw120RC.allRC m hm) (by decide)
  · exact widen (BB6.Agent3Raw120.allRF m hm) (by decide)
  · exact widen (BB6.Agent3Raw120OneLA.allOneLA m hm) (by decide)
  · exact widen (BB6.Agent3Raw120OneLB.allOneLB m hm) (by decide)
  · exact widen (BB6.Agent3Raw120OneLF.allOneLF m hm) (by decide)
  · exact widen (BB6.Agent3Raw120OneRA.allOneRA m hm) (by decide)
  · exact widen (BB6.Agent3Raw120OneRB.allOneRB m hm) (by decide)
  · exact widen (BB6.Agent3Raw120OneRC.allOneRC m hm) (by decide)
  · exact widen (BB6.Agent3Raw120OneRF.allOneRF m hm) (by decide)

theorem allRaw120 (m : Machine) (hm : compatible p120 m) : WeightedBound 224707 m :=
  allChildren (m hole) (choices_complete _) m (compatible_refine p120 m hole hm)

theorem coverRaw120 (B : Nat) (hB : 224707 ≤ B) : Cover (WeightedBound B) p120 :=
  Cover.leaf _ (fun m hm => widen (allRaw120 m hm) hB)

#print axioms allRaw120
#print axioms coverRaw120

end BB6.Agent3Raw120Complete
