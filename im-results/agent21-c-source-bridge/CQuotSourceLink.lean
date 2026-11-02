import QuotientArithmetic
import CLine
import Lean.Elab.Tactic.Omega

namespace BB6.CQuotSourceLink

/-- The normalized transition function used by Agent 20's quotient proof
    equals the published, machine-bridged CLine transition function. -/
theorem nextC_eq_source (a k c : Nat) :
    Agent20CQuot.nextC a k c = BB6CLine.nextC (a,k,c) := by
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · simp [Agent20CQuot.nextC, BB6CLine.nextC]
    · rcases k with _ | k <;> simp [Agent20CQuot.nextC, BB6CLine.nextC] <;> omega
    · simp [Agent20CQuot.nextC, BB6CLine.nextC] <;> omega
  · simp [Agent20CQuot.nextC, BB6CLine.nextC]
  · simp [Agent20CQuot.nextC, BB6CLine.nextC]
  · simp [Agent20CQuot.nextC, BB6CLine.nextC]
  · rcases a with _ | a
    · by_cases h : k%2=0
      · simp [Agent20CQuot.nextC, BB6CLine.nextC,h] <;> omega
      · simp [Agent20CQuot.nextC, BB6CLine.nextC,h] <;> omega
    · simp [Agent20CQuot.nextC, BB6CLine.nextC] <;> omega

/-- Agent 20's one-step quotient preservation applies to CLine itself. -/
theorem source_representative (a k c : Nat) :
  Option.map Agent20CQuot.quotientTrip
    (BB6CLine.nextC (Agent20CQuot.rep a, Agent20CQuot.rep k, Agent20CQuot.rep c)) =
  Option.map Agent20CQuot.quotientTrip (BB6CLine.nextC (a,k,c)) := by
  rw [←nextC_eq_source, ←nextC_eq_source]
  exact Agent20CQuot.nextC_representative a k c

#print axioms nextC_eq_source
#print axioms source_representative

end BB6.CQuotSourceLink
