import Lean.Elab.Tactic.Omega
import ETripleLadderIndex

namespace BB6.ETripleLadderSafe
open CryptidBoundary
open BB6.ETripleLadderSource
open BB6.ETripleLadderIndex
set_option maxHeartbeats 4000000

private theorem halt_stable (c : Cfg) (hc : c.st=6) :
    (step c).st=6 := by
  cases c with
  | mk l h r st =>
    simp only at hc
    subst st
    cases h <;> simp [step]

private theorem run_halt_stable (n : Nat) (c : Cfg) (hc : c.st=6) :
    (run n c).st=6 := by
  induction n generalizing c with
  | zero => simpa [run] using hc
  | succ n ih =>
    change (run n (step c)).st=6
    exact ih (step c) (halt_stable c hc)

/-- Every primitive time through the closed-form E-ladder endpoint is safe
    from the absorbing source halt state, for all parameters and suffixes. -/
theorem ladder_no_halt (m u q : Nat) (ys : List Bool) (t : Nat)
    (ht : t≤totalCost m u q) :
    (run t (physicalSection (3^(m+1)*(u+1)+1) q m ys)).st≠6 := by
  let start := physicalSection (3^(m+1)*(u+1)+1) q m ys
  have hfin : (run (totalCost m u q) start).st = 5 := by
    rw [power_ladder_source]
    simp [physicalSection]
  intro hbad
  have htime : totalCost m u q = t+(totalCost m u q-t) := by omega
  rw [htime,run_add] at hfin
  have hst := run_halt_stable (totalCost m u q-t) (run t start) hbad
  omega

#print axioms ladder_no_halt
end BB6.ETripleLadderSafe
