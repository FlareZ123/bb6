import Agent46Raw13Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Branch540
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent46Raw13
def pA := child ⟨false,true,2⟩
def pC := refine pA (2,true) (some ⟨false,false,2⟩)
def parent := refine pC (1,true) (some ⟨false,false,3⟩)
theorem parent_support : TNFSupport parent 4 := by
  have ha : TNFSupport pA 3 :=
    refine_support raw13 (0,true) ⟨false,true,2⟩ 3 3 raw13_support (by decide) (by decide) (by decide)
  have hc : TNFSupport pC 3 :=
    refine_support pA (2,true) ⟨false,false,2⟩ 3 3 ha (by decide) (by decide) (by decide)
  exact refine_support pC (1,true) ⟨false,false,3⟩ 3 4 hc (by decide) (by decide) (by decide)
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (weightedTNFNoAssignedHalt_refine _ _ _ raw13_nohalt))
def next (mv : Move) := refine parent (3,true) (some mv)
theorem compatible_quotient (m : Machine) (hm : compatible parent m) :
    TNFQuotientCompatible parent m := by
  let e : StatePerm := ⟨id,id,fun _ => rfl,fun _ => rfl⟩
  refine ⟨e,rfl,?_⟩
  have he : renameTable e m = m := by
    funext s
    rcases s with ⟨q,b⟩
    unfold renameTable
    change (m (q,b)).map (renameMove e) = m (q,b)
    cases h : m (q,b) with
    | none => rfl
    | some mv => cases mv <;> rfl
  rw [he]
  exact hm
end BB6.Agent46Raw13Branch540
