import Agent46Raw13Data
import Agent46Raw13Branch484
import Agent46Raw13Branch540
import Agent46Raw13Branch830
import Agent46Raw13Branch1420
import Agent46Raw13Branch1422
import Agent46Raw13Branch503
import Agent46Raw13Branch1046
import Agent46Raw13Branch231
import Agent46Raw13Branch323
import Agent46Raw13Branch321
import Agent46Raw13Branch482
import Agent46Raw13Branch682
import Agent46Raw13Branch1100
import Agent46Raw13Branch601395
import Agent46Raw13Branch601452
import Agent46Raw13Branch601541
import Agent46Raw13Branch601396
import Agent46Raw13Branch600489
import Agent46Raw13Branch600542
import Agent46Raw13Branch600571
import Agent46Raw13Branch600573
import Agent46Raw13Branch601454
import Agent46Raw13Branch601456
import Agent46Raw13Branch601558

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw1324ParentGraft
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent46Raw13 BB6.Agent31ThreeHole

def closedParents : List PartialMachine := [
  Agent46Raw13Branch484.parent,
  Agent46Raw13Branch540.parent,
  Agent46Raw13Branch830.parent,
  Agent46Raw13Branch1420.parent,
  Agent46Raw13Branch1422.parent,
  Agent46Raw13Branch503.parent,
  Agent46Raw13Branch1046.parent,
  Agent46Raw13Branch231.parent,
  Agent46Raw13Branch323.parent,
  Agent46Raw13Branch321.parent,
  Agent46Raw13Branch482.parent,
  Agent46Raw13Branch682.parent,
  Agent46Raw13Branch1100.parent,
  Agent46Raw13Branch601395.parent,
  Agent46Raw13Branch601452.parent,
  Agent46Raw13Branch601541.parent,
  Agent46Raw13Branch601396.parent,
  Agent46Raw13Branch600489.parent,
  Agent46Raw13Branch600542.parent,
  Agent46Raw13Branch600571.parent,
  Agent46Raw13Branch600573.parent,
  Agent46Raw13Branch601454.parent,
  Agent46Raw13Branch601456.parent,
  Agent46Raw13Branch601558.parent]

theorem parent_bound (p : PartialMachine) (hp : p ∈ closedParents)
    (m : Machine) (hm : compatible p m) : WeightedBound 7014 m := by
  simp only [closedParents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Agent46Raw13Branch484.bound m hm
  · exact Agent46Raw13Branch540.bound m hm
  · exact Agent46Raw13Branch830.bound m hm
  · exact Agent46Raw13Branch1420.bound m hm
  · exact Agent46Raw13Branch1422.bound m hm
  · exact Agent46Raw13Branch503.bound m hm
  · exact Agent46Raw13Branch1046.bound m hm
  · exact Agent46Raw13Branch231.bound m hm
  · exact Agent46Raw13Branch323.bound m hm
  · exact Agent46Raw13Branch321.bound m hm
  · exact Agent46Raw13Branch482.bound m hm
  · exact Agent46Raw13Branch682.bound m hm
  · exact Agent46Raw13Branch1100.bound m hm
  · exact Agent46Raw13Branch601395.bound m hm
  · exact Agent46Raw13Branch601452.bound m hm
  · exact Agent46Raw13Branch601541.bound m hm
  · exact Agent46Raw13Branch601396.bound m hm
  · exact Agent46Raw13Branch600489.bound m hm
  · exact Agent46Raw13Branch600542.bound m hm
  · exact Agent46Raw13Branch600571.bound m hm
  · exact Agent46Raw13Branch600573.bound m hm
  · exact Agent46Raw13Branch601454.bound m hm
  · exact Agent46Raw13Branch601456.bound m hm
  · exact Agent46Raw13Branch601558.bound m hm

theorem parent_first (p : PartialMachine) (hp : p ∈ closedParents) :
    p initialSlot = some (some ⟨true,true,1⟩) := by
  simp only [closedParents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def isClosed (p : PartialMachine) : Bool := closedParents.any (tableOK p)
def remaining : List (List Move × PartialMachine) :=
  raw13Residuals.filter (fun e => !isClosed e.2)

theorem refined_sound (m : Machine) (hm : TNFQuotientCompatible raw13 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  rcases raw13_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · cases h : isClosed e.2 with
    | false =>
      exact Or.inr ⟨e,List.mem_filter.mpr ⟨he, by simp [h]⟩,hq⟩
    | true =>
      have ha : closedParents.any (tableOK e.2) = true := h
      obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp ha
      have hEq := tableOK_sound e.2 p ht
      have hb := safe_quotient (parent_first p hp) (parent_bound p hp) m (hEq ▸ hq)
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))

theorem refined_count : remaining.length = 1684 := by decide

#print axioms refined_sound
#print axioms refined_count
end BB6.Agent46Raw1324ParentGraft
