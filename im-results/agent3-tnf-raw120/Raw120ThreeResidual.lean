import Raw120EasyCycles
import Raw120LAData
import Raw120ZeroLBData
import Raw120ZeroLFData
import Raw120RAData
import Raw120RBData
import Raw120RCData
import Raw120RFData
import Raw120OneLAData
import Raw120OneLFData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120ThreeResidual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent3Raw120 BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent31ThreeHole BB6.Agent3Raw120EasyCycles

/-- The three ordinary branches not consumed by the eleven accepted
    noncycle sibling certificates. -/
def remaining : List Transition :=
  [some ⟨true,false,1⟩, some ⟨true,true,2⟩, some ⟨true,true,5⟩]

def covered : List Transition := choices.filter (fun t => decide (t ∉ remaining))

theorem remaining_count : remaining.length = 3 := by decide
theorem covered_count : covered.length = 22 := by decide
theorem remaining_nodup : remaining.Nodup := by decide
theorem covered_mass : ((covered.map fun t => cylinderMass (refine p120 hole t)).sum) = 22*25^5 := by decide
theorem remaining_mass : ((remaining.map fun t => cylinderMass (refine p120 hole t)).sum) = 3*25^5 := by decide
theorem mass_total : cylinderMass p120 = 25^6 := by decide

theorem children_disjoint (t u : Transition) (hne : t ≠ u) (m : Machine) :
    ¬ (compatible (refine p120 hole t) m ∧ compatible (refine p120 hole u) m) := by
  intro ⟨ht,hu⟩
  have ht' := ((compatible_refine_iff p120 m hole (by decide) t).mp ht).2
  have hu' := ((compatible_refine_iff p120 m hole (by decide) u).mp hu).2
  exact hne (ht'.symm.trans hu')

theorem immediate_halt_checked : zipQueryOK 15 p120 9 hole = true := by decide

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

private def ordinaryCovered : List Transition :=
  [some ⟨false,false,0⟩, some ⟨false,false,1⟩, some ⟨false,false,5⟩,
   some ⟨false,true,0⟩, some ⟨false,true,1⟩, some ⟨false,true,2⟩,
   some ⟨false,true,5⟩, some ⟨true,false,0⟩, some ⟨true,false,5⟩,
   some ⟨true,true,0⟩, some ⟨true,true,1⟩]

private theorem partition_checked :
    (covered.filter (fun t => decide (t ≠ none ∧ t ∉ cycleChoices))).all
      (fun t => decide (t ∈ ordinaryCovered)) = true := by decide

/-- Nine child certificates are imported from the original checked matrix
    artifacts. The two earlier source-accepted siblings are explicit inputs
    to avoid requiring another generation or compile of their source closures. -/
theorem covered_bound
    (hRA : ∀ m, compatible (refine p120 hole (some ⟨true,true,0⟩)) m → WeightedBound 13317 m)
    (hRB : ∀ m, compatible (refine p120 hole (some ⟨true,true,1⟩)) m → WeightedBound 749 m)
    (t : Transition) (ht : t ∈ covered) (m : Machine)
    (hm : compatible (refine p120 hole t) m) : WeightedBound 18859 m := by
  by_cases hhalt : t = none
  · subst t
    exact widen (immediate_halt_bound m hm) (by decide)
  by_cases hc : t ∈ cycleChoices
  · exact widen (cycles_sound t hc m hm) (by decide)
  have hf : t ∈ covered.filter (fun u => decide (u ≠ none ∧ u ∉ cycleChoices)) :=
    List.mem_filter.mpr ⟨ht, by simpa using And.intro hhalt hc⟩
  have hn : t ∈ ordinaryCovered := of_decide_eq_true (List.all_eq_true.mp partition_checked t hf)
  simp only [ordinaryCovered,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  all_goals subst t
  · exact widen (BB6.Agent3Raw120LA.allLA m hm) (by decide)
  · exact widen (BB6.Agent3Raw120ZeroLB.allZeroLB m hm) (by decide)
  · exact widen (BB6.Agent3Raw120ZeroLF.allZeroLF m hm) (by decide)
  · exact widen (BB6.Agent3Raw120RA.allRA m hm) (by decide)
  · exact widen (BB6.Agent3Raw120RB.allRB m hm) (by decide)
  · exact widen (BB6.Agent3Raw120RC.allRC m hm) (by decide)
  · exact widen (BB6.Agent3Raw120.allRF m hm) (by decide)
  · exact widen (BB6.Agent3Raw120OneLA.allOneLA m hm) (by decide)
  · exact widen (BB6.Agent3Raw120OneLF.allOneLF m hm) (by decide)
  · exact widen (hRA m hm) (by decide)
  · exact widen (hRB m hm) (by decide)

/-- All compatible machines belong to the already bounded complement or one
    of exactly three explicitly named, pairwise disjoint child cylinders. -/
theorem parent_partition
    (hRA : ∀ m, compatible (refine p120 hole (some ⟨true,true,0⟩)) m → WeightedBound 13317 m)
    (hRB : ∀ m, compatible (refine p120 hole (some ⟨true,true,1⟩)) m → WeightedBound 749 m)
    (m : Machine) (hm : compatible p120 m) : WeightedBound 18859 m ∨
      ∃ t ∈ remaining, compatible (refine p120 hole t) m := by
  have hchild := compatible_refine p120 m hole hm
  by_cases hr : m hole ∈ remaining
  · exact Or.inr ⟨m hole,hr,hchild⟩
  · have ht : m hole ∈ covered := List.mem_filter.mpr ⟨choices_complete _, by simpa using hr⟩
    exact Or.inl (covered_bound hRA hRB (m hole) ht m hchild)

/-- Complete parent closure is reduced to the three remaining child Covers. -/
theorem cover_from_three (B : Nat) (hB : 18859 ≤ B)
    (hRA : ∀ m, compatible (refine p120 hole (some ⟨true,true,0⟩)) m → WeightedBound 13317 m)
    (hRB : ∀ m, compatible (refine p120 hole (some ⟨true,true,1⟩)) m → WeightedBound 749 m)
    (hLeaves : ∀ t ∈ remaining, Cover (WeightedBound B) (refine p120 hole t)) :
    Cover (WeightedBound B) p120 := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases parent_partition hRA hRB m hm with h | ⟨t,ht,hc⟩
  · exact widen h hB
  · exact (hLeaves t ht).sound m hc

#print axioms remaining_count
#print axioms covered_count
#print axioms covered_mass
#print axioms remaining_mass
#print axioms children_disjoint
#print axioms immediate_halt_bound
#print axioms parent_partition
#print axioms cover_from_three
end BB6.Agent3Raw120ThreeResidual
