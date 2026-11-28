import Raw13CoupledParent

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled7ZeroLA
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent50TNFPilot BB6.Agent10ZipAudit
open BB6.Agent46Raw13CoupledParent

abbrev parent := refine p2 (2,true) (some ⟨false,false,0⟩)
def parentCut : Cut := .closed (.cycle 3 5 false 1)

theorem parent_support : TNFSupport parent 4 := by
  have h1 : TNFSupport p1 4 :=
    refine_support BB6.Agent46Raw13.raw13 (0,true) ⟨true,false,3⟩ 3 4
      BB6.Agent46Raw13.raw13_support (by decide) (by decide) (by decide)
  have h2 : TNFSupport p2 4 :=
    refine_support p1 (3,true) ⟨false,false,0⟩ 4 4 h1
      (by decide) (by decide) (by decide)
  exact refine_support p2 (2,true) ⟨false,false,0⟩ 4 4 h2
    (by decide) (by decide) (by decide)

theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent46Raw13.raw13_nohalt))

theorem checked : check 0 parent 4 parentCut = true := by rfl
theorem complete : closedCut 4 parentCut = true := by rfl
theorem empty_complement : residuals parent 4 parentCut = [] :=
  residuals_empty_of_closedCut complete

theorem bound_quotient (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound 0 m := by
  rcases sound 0 parent 4 parentCut (by decide) parent_support (by decide)
      parent_nohalt checked m hm with hb | ⟨e,he,_⟩
  · exact hb
  · rw [empty_complement] at he
    simp at he

theorem bound (m : Machine) (hm : compatible parent m) : WeightedBound 0 m := by
  let e : StatePerm := ⟨id,id,fun _ => rfl,fun _ => rfl⟩
  apply bound_quotient m
  refine ⟨e,rfl,?_⟩
  have he : renameTable e m = m := by
    funext s
    rcases s with ⟨q,b⟩
    unfold renameTable
    change (m (q,b)).map (renameMove e) = m (q,b)
    cases hh : m (q,b) with
    | none => rfl
    | some mv => cases mv <;> rfl
  rw [he]
  exact hm

#print axioms checked
#print axioms bound_quotient
#print axioms bound
end BB6.Agent46Raw13Coupled7ZeroLA
