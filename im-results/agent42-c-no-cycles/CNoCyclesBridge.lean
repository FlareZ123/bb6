import CNoCycles
import CLine

namespace BB6Agent42

theorem source_next_agrees (s : S) : nextC s = BB6CLine.nextC s := by
  rfl

def sourceRun : Nat → Option S → Option S
  | 0, o => o
  | n+1, o => sourceRun n (o.bind BB6CLine.nextC)

theorem source_run_agrees (n : Nat) (o : Option S) :
    sourceRun n o = run n o := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
      simp only [sourceRun,run]
      rw [show o.bind BB6CLine.nextC = o.bind nextC from by
        cases o with
        | none => rfl
        | some s => simp [source_next_agrees]]
      exact ih _

theorem source_no_positive_cycle (s : S) (n : Nat) :
    sourceRun (n+1) (some s) ≠ some s := by
  rw [source_run_agrees]
  exact no_positive_cycle s n

theorem source_rank_growth_after_rank (s t : S)
    (h : sourceRun (rank s + 1) (some s) = some t) :
    rank s < rank t := by
  rw [source_run_agrees] at h
  exact rank_growth_after_rank s t h

#print axioms source_no_positive_cycle
#print axioms source_rank_growth_after_rank
end BB6Agent42
