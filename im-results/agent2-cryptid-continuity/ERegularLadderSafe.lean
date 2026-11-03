import Lean.Elab.Tactic.Omega
import ERegularLadderSource

namespace BB6.ERegularLadderSafe
open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.ERegularLadderSource BB6.EThirdSource
open BB6.Agent31SecondSource BB6.ETripleLadderSource
open BB6.ETripleLadderIndex

private theorem halt_step_stable (c : Cfg) (hc : c.st=6) :
    (step c).st=6 := by
  cases c with
  | mk l h r st =>
    simp only at hc
    subst st
    cases h <;> simp [step]

private theorem halt_run_stable (n : Nat) (c : Cfg)
    (hc : c.st=6) : (run n c).st=6 := by
  induction n generalizing c with
  | zero => simpa [run] using hc
  | succ n ih =>
    change (run n (step c)).st=6
    exact ih (step c) (halt_step_stable c hc)

/-- A physically equivalent F/0 checkpoint at raw time T proves that no
    absorbing raw halt can have occurred at any earlier primitive time. -/
theorem source_no_halt_to_endpoint (c d : Cfg) (T t : Nat)
    (ht : t ≤ T)
    (heq : ObsEq (run T c) d)
    (hfinal : d.st ≠ 6) :
    (run t c).st ≠ 6 := by
  have hstate : (run T c).st = d.st := heq.2.2.2
  intro hbad
  have htime : T=t+(T-t) := by omega
  have hlate : (run T c).st=6 := by
    rw [htime, run_add]
    exact halt_run_stable (T-t) (run t c) hbad
  exact hfinal (hstate.symm ▸ hlate)

/-- Source-connected absence of primitive halting through all three
    E-branch preliminary checkpoints and every later E-ladder step. -/
theorem odd_chain_no_halt (v h m u : Nat)
    (hn : 512*v+257 = 3^(m+1)*(u+1)+1)
    (hp : 2*h = 3*m+3)
    (t : Nat)
    (ht : t ≤ (firstCost (3*v+1) h + secondCost (3*v+1) +
         thirdCost v) + totalCost m u 4) :
    (run t (start (3*v+1) h)).st ≠ 6 := by
  have hs := original_E_then_ladder v h m u hn hp
  exact source_no_halt_to_endpoint
    (start (3*v+1) h)
    (physicalSection (3*8^m*(u+1)+1) (4+2*m) 0
      (List.replicate 6 true))
    ((firstCost (3*v+1) h + secondCost (3*v+1) +
       thirdCost v) + totalCost m u 4)
    t ht hs (by simp [physicalSection])

/-- Identical source-connected nonhalting-prefix certificate for the
    complementary B-branch preliminary third checkpoint. -/
theorem even_chain_no_halt (v h m u : Nat)
    (hn : 512*v+434 = 3^(m+1)*(u+1)+1)
    (hp : 2*h+3 = 3*m+3)
    (t : Nat)
    (ht : t ≤ (firstCost (3*v+2) h + secondCost (3*v+2) +
        thirdBCost v) + totalCost m u 1) :
    (run t (start (3*v+2) h)).st ≠ 6 := by
  have hs := original_B_then_ladder v h m u hn hp
  exact source_no_halt_to_endpoint
    (start (3*v+2) h)
    (physicalSection (3*8^m*(u+1)+1) (1+2*m) 0
      (List.replicate 6 true))
    ((firstCost (3*v+2) h + secondCost (3*v+2) +
       thirdBCost v) + totalCost m u 1)
    t ht hs (by simp [physicalSection])

#print axioms source_no_halt_to_endpoint
#print axioms odd_chain_no_halt
#print axioms even_chain_no_halt
end BB6.ERegularLadderSafe
