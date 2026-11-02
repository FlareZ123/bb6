import Lean.Elab.Tactic.Omega
import CryptidSix

set_option maxHeartbeats 10000000
set_option maxRecDepth 1024

namespace BB6.Agent32EZero

open CryptidBoundary

def packetZero : List Bool :=
  [false,true,true,true,true,false,true,false,true,false,true,false]

/-- Distinct zero-pair E branch, inapplicable to the q>=1 EDouble theorem. -/
def eZero (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+3) ++ [true,true], false,
    [true,true,false,false] ++ ys, 4⟩

/-- Bounded 60-transition turn, independent of the remaining m left pairs. -/
theorem eZero_front (m : Nat) (ys : List Bool) :
    run 60 (eZero m ys) = sweepB m (packetZero ++ ys) := by
  simp [eZero, sweepB, packetZero, run, step, goL, goR, pairs]

/-- Every zero-pair E-1100 boundary yields a complete F return. -/
theorem eZero_run (m : Nat) (ys : List Bool) :
    run (2*m+63) (eZero m ys) =
      ⟨[],false,List.replicate (2*m+3) true ++ (packetZero ++ ys),5⟩ := by
  have ht : 2*m+63 = 60+(2*m+3) := by omega
  rw [ht, run_add, eZero_front, sweepB_run]

/-- New original-machine complete F-section return for E input 0 1100,
    without a preceding (10) pair and with arbitrary suffix. -/
theorem full_E_zero_pairs (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+96)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,false,false] ++ ys))) =
    ⟨[],false,List.replicate (8*k+3) true ++ (packetZero ++ ys),5⟩ := by
  have ht : 12*k*k+49*k+96 =
      (12*k*k+41*k+33)+(2*(4*k)+63) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k)+63) (eZero (4*k) ys) = _
  rw [eZero_run]
  rw [show 2*(4*k)+3 = 8*k+3 by omega]

#print axioms eZero_front
#print axioms eZero_run
#print axioms full_E_zero_pairs
end BB6.Agent32EZero
