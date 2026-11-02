import Lean.Elab.Tactic.Omega
import CryptidSix

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- The genuine implicit blank beyond six ones is represented by the
    empty finite-list suffix, rather than the extra explicit zero in eSix. -/
def eSixBlank (m : Nat) : Cfg :=
  ⟨false::false::pairs m ++ [true,true], false,
    List.replicate 6 true, 4⟩

def packetSixBlank : List Bool :=
  [false,true,false,true,false,true,true,true]

theorem eSixBlank_front (m : Nat) :
    run 16 (eSixBlank m) = sweepB m packetSixBlank := by
  simp [eSixBlank, sweepB, packetSixBlank, run, step, goL, goR, pairs]

theorem eSixBlank_run (m : Nat) :
    run (2*m+19) (eSixBlank m) =
      ⟨[],false,List.replicate (2*m+3) true ++ packetSixBlank,5⟩ := by
  have ht : 2*m+19 = 16+(2*m+3) := by omega
  rw [ht, run_add, eSixBlank_front, sweepB_run]

/-- Exact original-source F section return without appending a fabricated
    explicit final zero to the six ones. -/
theorem full_E_six_blank (k : Nat) :
    run (12*k*k+49*k+58)
      (init (List.replicate (3*k+2) true ++
        false :: List.replicate 6 true)) =
    ⟨[],false,List.replicate (8*k+9) true ++ packetSixBlank,5⟩ := by
  have ht : 12*k*k+49*k+58 =
      (12*k*k+41*k+33)+(2*(4*k+3)+19) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k+3)+19) (eSixBlank (4*k+3)) = _
  rw [eSixBlank_run]
  rw [show 2*(4*k+3)+3=8*k+9 by omega]

#print axioms eSixBlank_front
#print axioms eSixBlank_run
#print axioms full_E_six_blank
end CryptidBoundary
