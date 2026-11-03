import BlankMassStandalone
import Lean.Elab.Tactic.Omega

namespace CFiniteReach

def maxIndex (a k : Nat) : Nat := (a+2*k-7)/4

/-- Total finite Boolean reachability decider for each fixed target in the
    transcribed original Machine C section model. Potentially very expensive. -/
def reachableBool (a k : Nat) : Bool := decide
  (∃ i : Fin (maxIndex a k+1),
    ForwardMass.run ForwardC.secNext (5,1) i.val = some (a,k))

theorem reachableBool_correct (a k : Nat) :
  reachableBool a k = true ↔
    ∃ n : Nat, ForwardMass.run ForwardC.secNext (5,1) n = some (a,k) := by
  simp only [reachableBool, decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i.val,hi⟩
  · rintro ⟨n,hn⟩
    have hb := BlankMassStandalone.blank_index_bound n a k hn
    refine ⟨⟨n,by simpa only [maxIndex] using Nat.lt_succ_of_le hb⟩,hn⟩

#print axioms reachableBool_correct
end CFiniteReach
