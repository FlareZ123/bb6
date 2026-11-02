import Lean.Elab.Tactic.Omega
import BlankTrace
import EEmpty

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- Genuine blank orbit: another 2-mod-3 pure-unary return. -/
theorem blank468794 : run 468794 blank = init (List.replicate 1455 true) := by
  have ht : 468794=66753+(12*181*181+49*181+40) := by decide
  rw [ht, run_add, blank66753]
  simpa [init] using full_B_nil 181

/-- Genuine blank orbit: another 2-mod-3 pure-unary return. -/
theorem blank3315299 : run 3315299 blank = init (List.replicate 3887 true) := by
  have ht : 3315299=468794+(12*485*485+49*485+40) := by decide
  rw [ht, run_add, blank468794]
  simpa [init] using full_B_nil 485

/-- First genuine blank-origin E return, with the exact nonuniform trailing word. -/
theorem blank23503104 :
    run 23503104 blank = init
      (List.replicate 10363 true ++ false :: List.replicate 6 true) := by
  have ht : 23503104=3315299+(12*1295*1295+49*1295+50) := by decide
  rw [ht, run_add, blank3315299]
  simpa only [Nat.reduceMul,Nat.reduceAdd] using full_E_nil 1295

#print axioms blank468794
#print axioms blank3315299
#print axioms blank23503104
end CryptidBoundary
