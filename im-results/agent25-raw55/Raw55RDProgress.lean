import Raw55RDData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw55RDProgress
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent19CanonicalPartial
open BB6.Agent25Raw55RD
open BB6.Agent25Raw55Progress (equalTable equalTable_sound)

def moves : List Move := [⟨false,false,5⟩,⟨false,true,5⟩,⟨true,false,0⟩,
    ⟨true,false,1⟩,⟨true,false,5⟩,⟨true,true,5⟩]
def child (mv : Move) : PartialMachine := refine rdParent (4,false) (some mv)
def matches (p : PartialMachine) : Bool := moves.any (fun mv => equalTable p (child mv))
def remaining := BB6.Agent25Raw55Progress.remaining.filter (fun e => !matches e.2)
theorem remaining_count : remaining.length = 265 := by decide

theorem childSafe (mv : Move) (m : Machine) (hm : TNFQuotientCompatible (child mv) m) :
    WeightedBound 7014 m := by
  have hr : child mv initialSlot = some (some ⟨true,true,1⟩) := by rfl
  exact quotientSafe hr (fun m hc => all_rd m
    (refine_preserves_compat rdParent m (4,false) (some mv) (by decide) hc)) m hm

theorem refined (m : Machine) (hm : TNFQuotientCompatible BB6.Agent25Raw55Cut.parent m) :
    WeightedBound 7014 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  rcases BB6.Agent25Raw55Progress.refined m hm with h | ⟨e,he,hq⟩
  · exact Or.inl h
  · cases hh : matches e.2 with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hh]⟩,hq⟩
    | true =>
      obtain ⟨mv,_,hmatch⟩ := List.any_eq_true.mp hh
      have eq := equalTable_sound hmatch
      rw [eq] at hq
      exact Or.inl (childSafe mv m hq)
#print axioms remaining_count
#print axioms childSafe
#print axioms refined
end BB6.Agent25Raw55RDProgress
