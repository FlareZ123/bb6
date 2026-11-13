import TM63RootQ4Attainable
import M1EvenQ4Suffix
import Lean.Elab.Tactic.Omega

/-!
# TM63 root composition through the first m=1,n=6 reset

The blank-root q4/drain theorem already reaches
S1(3,6,1,71,0,2^63-1).  Agent 42's source composition proves the next
complete proposed increment, including its counted drain, and this module
factors that first increment out of the remaining conditional itinerary.
-/

namespace BB6Coverage.Agent42M1EvenRootComposition

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42M1EvenSuffix
open BB6ChampionArithmetic

/-- Exact S1 parameters immediately after the first m=1,n=6 increment. -/
def tm63AfterM1EvenA : Nat := 71+(2^63-1)+2
def tm63AfterM1EvenB : Nat := nextRight (2^63-1)
def tm63AfterM1EvenHead : Int := (223:Int)+5+(3*(2^63-1):Nat)

private theorem tm63NextRight_eq (b : Nat) : nextRight b = 2^b-1 := by
  rfl

private theorem tm63SectionResult_succ_cost (n m a b : Nat) :
    (sectionResult (n+1) m a b).cost =
      proposedIncrementCost (m%3) (n+1) a b +
        (sectionResult n (nextMarker m) (nextExponent m a b) (nextRight b)).cost := by
  rfl

/-- The still-conditional itinerary after the newly source-proved first
m=1,n=6 increment. -/
def tm63AfterM1EvenSteps : Nat :=
  (sectionResult 5 0 tm63AfterM1EvenA tm63AfterM1EvenB).cost +
    resetCost 3 tm63FirstSection.exponent tm63FirstSection.right +
    tm63MiddleSection.cost +
    resetCost tm63Length1 tm63MiddleSection.exponent tm63MiddleSection.right +
    tm63LastPreSection.cost + 12*v2 tm63Index2

/-- The former suffix is exactly the proved first increment followed by
the residual conditional itinerary. -/
theorem tm63SuffixSteps_split_m1_even :
    tm63SuffixSteps =
      proposedIncrementCost 1 6 71 (2^63-1) + tm63AfterM1EvenSteps := by
  have hfirst :
      tm63FirstRest.cost =
        proposedIncrementCost 1 6 71 (2^63-1) +
          (sectionResult 5 0 tm63AfterM1EvenA tm63AfterM1EvenB).cost := by
    change (sectionResult 6 1 71 (2^63-1)).cost = _
    have hm : nextMarker 1 = 0 := by decide
    have ha : nextExponent 1 71 (2^63-1) = tm63AfterM1EvenA := by
      change 71+(2^63-1)+2 = 71+(2^63-1)+2
      rfl
    have hb : nextRight (2^63-1) = tm63AfterM1EvenB := by
      change nextRight (2^63-1) = nextRight (2^63-1)
      rfl
    calc
      (sectionResult 6 1 71 (2^63-1)).cost =
          proposedIncrementCost (1%3) 6 71 (2^63-1) +
            (sectionResult 5 (nextMarker 1) (nextExponent 1 71 (2^63-1))
              (nextRight (2^63-1))).cost :=
        tm63SectionResult_succ_cost 5 1 71 (2^63-1)
      _ = proposedIncrementCost 1 6 71 (2^63-1) +
            (sectionResult 5 0 tm63AfterM1EvenA tm63AfterM1EvenB).cost := by
        rw [hm,ha,hb]
        have hmod : 1%3 = 1 := by decide
        rw [hmod]
        rfl
  unfold tm63SuffixSteps tm63AfterM1EvenSteps
  rw [hfirst]
  omega

/-- The exact candidate-score theorem now requires only the remaining
five-stage itinerary from the marker-0 n=5 state, rather than the entire
continuation from the q4/drain endpoint. -/
theorem tm63_attainable_after_m1_even_q4
    (h : Int)
    (hstage :
      run tm2 tm63AfterM1EvenSteps
        (s1Config 3 5 0 tm63AfterM1EvenA 0 tm63AfterM1EvenB
          tm63AfterM1EvenHead) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h))
    (hfinal :
      run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
        (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) =
        some (s0Config (markerWord 0 ++ d0 ++ binDec tm63Length2 0 ++ lh)
          (tm63FinalA+tm63FinalB+resetDelta 1)
          (2^tm63FinalB-1) 0 h)) :
    Attainable proposedChampionScore := by
  have hfirst := m1Even_q4_counted_increment_source
    71 (2^63-1) 223 (by decide)
  have hfirst' :
      run tm2 (proposedIncrementCost 1 6 71 (2^63-1))
        (s1Config 3 6 1 71 0 (2^63-1) 223) =
        some (s1Config 3 5 0 tm63AfterM1EvenA 0
          tm63AfterM1EvenB tm63AfterM1EvenHead) := by
    have hcfg :
        s1Config 3 5 0 (71+(2^63-1)+2) 0
          (2^(2^63-1)-1) ((223:Int)+5+(3*(2^63-1):Nat)) =
        s1Config 3 5 0 tm63AfterM1EvenA 0
          tm63AfterM1EvenB tm63AfterM1EvenHead := by
      simp only [tm63AfterM1EvenA,tm63AfterM1EvenB,
        tm63AfterM1EvenHead,tm63NextRight_eq]
      congr 1 <;> try rfl
      omega
    exact hfirst.trans (congrArg some hcfg)
  have hstageFull :
      run tm2 tm63SuffixSteps
        (s1Config 3 6 1 71 0 (2^63-1) 223) =
        some (s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h) := by
    rw [tm63SuffixSteps_split_m1_even,run_add,hfirst']
    exact hstage
  exact tm63_attainable_at_proposedChampionScore h hstageFull hfinal

#print axioms tm63SuffixSteps_split_m1_even
#print axioms tm63_attainable_after_m1_even_q4

end BB6Coverage.Agent42M1EvenRootComposition
