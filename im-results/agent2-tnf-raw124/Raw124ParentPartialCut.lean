import Raw124ParentJoin
import Raw124Z0RAData
import Raw124Z0RFData
import Raw124Z0LCData
import Raw124Z0LDData
import Raw124Z0RCData
import Raw124Z0RDData
import Raw124Z0RBData
import Raw124Z1LCData
import Raw124Z1LEData
import Raw124Z1LFData
import Raw124Z1RAData
import Raw124Z1RBData
import Raw124Z1RCData
import Raw124Z1RDData
import Raw124Z1RFData
import Raw124ZeroLAComplete
import Raw124ZeroLBComplete
import Raw124New0LEComplete
import Raw124New1LA
import Raw124OneLBComplete
import Raw124Trivial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124ParentPartialCut

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16ResidualCover
open BB6.Agent32Raw124ParentJoin

/-- The largest of the 22 accepted F1 child bounds is the F1=0LB bound. -/
abbrev parentBound : Nat := 4136175

/-- All 22 currently source-accepted F1 child Covers, lifted to one bound. -/
def accepted : List (Accepted parentBound) :=
  [ liftAccepted (by decide) BB6.Agent32Raw124Z0RA.pBranch BB6.Agent32Raw124Z0RA.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z0RF.pBranch BB6.Agent32Raw124Z0RF.bound_all,
    liftAccepted (by decide) BB6.Agent2Raw124New0LA.branch BB6.Agent32Raw124ZeroLAComplete.bound_all,
    liftAccepted (by decide) BB6.Agent2Raw124New0LB.branch BB6.Agent2Raw124ZeroLBComplete.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z0LC.pBranch BB6.Agent32Raw124Z0LC.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z0LD.pBranch BB6.Agent32Raw124Z0LD.bound_all,
    liftAccepted (by decide) BB6.Agent2Raw124New0LE.branch BB6.Agent2Raw124New0LE.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z0RB.pBranch BB6.Agent32Raw124Z0RB.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z0RC.pBranch BB6.Agent32Raw124Z0RC.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z0RD.pBranch BB6.Agent32Raw124Z0RD.bound_all,
    liftAccepted (by decide) BB6.Agent2Raw124New1LA.branch BB6.Agent2Raw124New1LA.bound_all,
    liftAccepted (by decide) BB6.Agent2Raw124New1LB.branch BB6.Agent2Raw124OneLBComplete.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z1LC.pBranch BB6.Agent32Raw124Z1LC.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Trivial.p1LD BB6.Agent32Raw124Trivial.bound1LD,
    liftAccepted (by decide) BB6.Agent32Raw124Z1LE.pBranch BB6.Agent32Raw124Z1LE.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z1LF.pBranch BB6.Agent32Raw124Z1LF.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z1RA.pBranch BB6.Agent32Raw124Z1RA.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z1RB.pBranch BB6.Agent32Raw124Z1RB.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z1RC.pBranch BB6.Agent32Raw124Z1RC.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Z1RD.pBranch BB6.Agent32Raw124Z1RD.bound_all,
    liftAccepted (by decide) BB6.Agent32Raw124Trivial.p1RE BB6.Agent32Raw124Trivial.bound1RE,
    liftAccepted (by decide) BB6.Agent32Raw124Z1RF.pBranch BB6.Agent32Raw124Z1RF.bound_all ]

/-- The exact two uncovered F1 transitions are 0RE and 0LF; all other
    22 child tables match one of the source-accepted Covers above. -/
theorem covered_iff (mv : Move) :
    covered accepted (child mv) = true ↔
      mv ≠ (false,true,4) ∧ mv ≠ (false,false,5) := by decide

theorem covered_or_missing (mv : Move) :
    mv = (false,true,4) ∨ mv = (false,false,5) ∨
      covered accepted (child mv) = true := by
  by_cases hRE : mv = (false,true,4)
  · exact Or.inl hRE
  · by_cases hLF : mv = (false,false,5)
    · exact Or.inr (Or.inl hLF)
    · exact Or.inr (Or.inr ((covered_iff mv).2 ⟨hRE,hLF⟩))

/-- Once F1=0RE and F1=0LF are supplied at the common bound, the
    22 accepted siblings and the exact first-query halt case yield the
    complete Raw124 parent Cover. -/
theorem cover_of_two
    (h0RE : ∀ m, compatible (child (false,true,4)) m → WeightedBound parentBound m)
    (h0LF : ∀ m, compatible (child (false,false,5)) m → WeightedBound parentBound m) :
    Cover (WeightedBound parentBound) parent124 := by
  apply cover_of_children parentBound (by decide)
  intro mv m hm
  rcases covered_or_missing mv with hRE | hLF | hcovered
  · exact h0RE m (by simpa [hRE] using hm)
  · exact h0LF m (by simpa [hLF] using hm)
  · exact covered_sound hcovered m (by simpa [child] using hm)

/-- The two remaining child tables, named for downstream integration. -/
abbrev child0RE : PartialMachine := child (false,true,4)
abbrev child0LF : PartialMachine := child (false,false,5)

#print axioms covered_iff
#print axioms cover_of_two

end BB6.Agent2Raw124ParentPartialCut
