import Raw58MoreCut
import Raw58RCData
import Raw58LA1Data
import Raw58LB1Data
import Raw58RF1Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw58MoreCut2
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent4Raw58MoreCut
open BB6.Agent50RecursiveResidual

/-- The four additional first-hole cylinders closed by the source-audited
    RC, LA1, LB1, and RF1 children. Five five-hole cylinders remain. -/
def remaining : List Move :=
  BB6.Agent4Raw58MoreCut.remaining.filter fun mv =>
    decide (mv ≠ ⟨false,true,2⟩ ∧
      mv ≠ ⟨true,false,0⟩ ∧
      mv ≠ ⟨true,false,1⟩ ∧
      mv ≠ ⟨true,true,5⟩)

theorem remaining_count : remaining.length = 5 := by decide

theorem first_query : BB6.Agent50RecursiveResidual.queryOK 374 parent 7 (0,true) = true := by
  decide

/-- Compose the accepted 156-bound three-child cut with four further
    complete child certificates. The only remaining first-hole actions are
    0LE, 0LF, 0RF, 1LE, and 1LF. -/
theorem parent_dichotomy (m : Machine) (hm : compatible parent m) :
    WeightedBound 374 m ∨ ∃ mv ∈ remaining, compatible (child mv) m := by
  rcases BB6.Agent4Raw58MoreCut.parent_dichotomy m hm with hb | ⟨mv,hr,hc⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hRC : mv = ⟨false,true,2⟩
    · subst mv
      exact Or.inl (fun k d hk hd =>
        Nat.le_trans (BB6.Agent4Raw58RC.certificate.sound m hc k d hk hd) (by decide))
    · by_cases hLA : mv = ⟨true,false,0⟩
      · subst mv
        exact Or.inl (fun k d hk hd =>
          Nat.le_trans (BB6.Agent4Raw58LA1.all_completions m hc k d hk hd) (by decide))
      · by_cases hLB : mv = ⟨true,false,1⟩
        · subst mv
          exact Or.inl (fun k d hk hd =>
            Nat.le_trans (BB6.Agent4Raw58LB1.all_completions m hc k d hk hd) (by decide))
        · by_cases hRF : mv = ⟨true,true,5⟩
          · subst mv
            exact Or.inl (BB6.Agent4Raw58RF1.all_completions m hc)
          · exact Or.inr ⟨mv, List.mem_filter.mpr
              ⟨hr, by simp [hRC,hLA,hLB,hRF]⟩, hc⟩

#print axioms remaining_count
#print axioms parent_dichotomy

end BB6.Agent4Raw58MoreCut2
