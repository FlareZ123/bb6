import Raw11Extra28After151
import Agent5Q0Coarse151
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact successor to the accepted Raw11 299→150 route.

The complete q0-151 parent is independently certified by the frozen
4,135,397-node first-hole proof. This module removes exactly that literal
parent from the accepted 150-entry Raw11 complement. No sibling is removed
except through exact sameTable equality.
-/
namespace BB6.Agent5Raw11Q0151After150
open BB6Coverage BB6.Agent13BlankDelay

def parent : PartialMachine := BB6.Agent5Q0Coarse151.parent
def prior : List PartialMachine := BB6.Agent47Raw11Extra28After151.remaining
def closed : List PartialMachine := [parent]
def remaining : List PartialMachine := Q0RosterConsume.removeCovered prior closed

theorem member_in_150 : parent ∈ prior := by
  have h : prior.any (fun q => Q0ExhaustiveTree.sameTable q parent) = true := by
    decide +kernel
  obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
  exact (Q0ExhaustiveTree.sameTable_sound he) ▸ hq

theorem remaining_census :
    (prior.length, remaining.length) = (150,149) := by
  decide +kernel

theorem parent_cover : Cover (WeightedBound 59642) parent :=
  BB6.Agent5Q0Coarse151.cover

theorem raw11_cover_from_149 (B : Nat) (hB : 59642 ≤ B)
    (hRemaining : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent :=
  BB6.Agent47Raw11Extra28After151.raw11_cover_from_150 B
    (Nat.le_trans (by decide : 4663 ≤ 59642) hB)
    (Q0RosterConsume.consume B prior closed
      (by
        intro p hp
        simp only [closed, List.mem_singleton] at hp
        subst p
        exact Q0RosterConsume.liftCover hB parent_cover)
      hRemaining)

#print axioms member_in_150
#print axioms remaining_census
#print axioms parent_cover
#print axioms raw11_cover_from_149
end BB6.Agent5Raw11Q0151After150
