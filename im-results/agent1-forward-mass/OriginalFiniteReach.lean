import BlankMassFour
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1ReachDecision
open BB6.Agent46

def maxIndex (a k : Nat) : Nat := (a+2*k-7)/4

/-- Finite Boolean decider for each individually specified original Machine C
    section target. It is neither efficient nor a BB(6) classification. -/
def reachableBool (a k : Nat) : Bool := decide
  (∃ i : Fin (maxIndex a k+1),
    BB6.Agent8Section.run secNext i.val (some (5,1)) = some (a,k))

theorem reachableBool_correct (a k : Nat) :
  reachableBool a k = true ↔
    ∃ n : Nat, BB6.Agent8Section.run secNext n (some (5,1)) = some (a,k) := by
  simp only [reachableBool, decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i.val,hi⟩
  · rintro ⟨n,hn⟩
    have hb := BB6.Agent1ForwardMass.blank_section_index_upper n a k hn
    refine ⟨⟨n,by simpa only [maxIndex] using Nat.lt_succ_of_le hb⟩,hn⟩

#print axioms reachableBool_correct
end BB6.Agent1ReachDecision
