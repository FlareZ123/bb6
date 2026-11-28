import HighBulkSource
import FarBulkSource
import SourceNextBridge

/-!
Uniform composition of the F321 source-counter High and Far accelerators
into arbitrarily long exact source-visible blocks. No per-step unfolding.
-/
namespace BB6.Agent2F321Bulk
open BB6.Agent31F321Density

theorem counter_reach_trans
    {a d A D B E j k:Nat}
    (h1:CounterReach a d j A D)
    (h2:CounterReach A D k B E) :
    CounterReach a d (j+k) B E := by
  induction h2 with
  | nil => simpa using h1
  | step hr hm ih =>
    simpa only [Nat.add_succ] using (CounterReach.step ih hm)

/-- One genuine arbitrarily long high block followed by a genuine
arbitrarily long far block, with only two exact scalar guard checks. -/
theorem high_then_far (a d j k:Nat)
    (hH:highCost d j≤a)
    (hF:farCost (a-highCost d j) k+1≤highD d j) :
    CounterReach a d (j+k)
       (farA (a-highCost d j) k)
       (highD d j-farCost (a-highCost d j) k) := by
  apply counter_reach_trans (high_bulk a d j hH)
  exact far_bulk (a-highCost d j) (highD d j) k hF

/-- Symmetric two-block certificate, Far then High. -/
theorem far_then_high (a d j k:Nat)
    (hF:farCost a j+1≤d)
    (hH:highCost (d-farCost a j) k≤farA a j) :
    CounterReach a d (j+k)
       (farA a j-highCost (d-farCost a j) k)
       (highD (d-farCost a j) k) := by
  apply counter_reach_trans (far_bulk a d j hF)
  exact high_bulk (farA a j) (d-farCost a j) k hH

/-- A complete source-counter epoch: a maximal or nonmaximal
arbitrarily long High block followed by one exact executable
sourceNext transition. A root-certificate generator supplies only
the High guard and the evaluated sourceNext branch, not individual
High trace entries. -/
theorem high_then_sourceNext {a d j A D:Nat}
    (h:highCost d j≤a)
    (hn:sourceNext (a-highCost d j) (highD d j)=some (A,D)) :
    CounterReach a d (j+1) A D := by
  have hb:=high_bulk a d j h
  have hm:=move_of_sourceNext_some hn
  have hseed : CounterReach (a-highCost d j) (highD d j) 0
      (a-highCost d j) (highD d j) := CounterReach.nil
  have htail : CounterReach (a-highCost d j) (highD d j) 1 A D := by
    simpa using (CounterReach.step hseed hm)
  have hboth:=counter_reach_trans hb htail
  simpa using hboth

#print axioms high_then_sourceNext

#print axioms counter_reach_trans
#print axioms high_then_far
#print axioms far_then_high
end BB6.Agent2F321Bulk
