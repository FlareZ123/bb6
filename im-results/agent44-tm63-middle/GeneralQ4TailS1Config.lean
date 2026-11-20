import GeneralQ4TailS1Reparam
import Lean.Elab.Tactic.Omega

/-!
# Direct q4Tail-to-S1 configuration equality for arbitrary A>=2

This composes the authentic q4Tail/S0 adapter with the generalized residual
reparameterization. It remains uncompiled pending local Lean preflight.
-/

namespace BB6Coverage.Agent44GeneralQ4TailReparam

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent38RootQ4TailS0
open BB6Coverage.Agent42FirstQ4P1Arithmetic

def q4TerminalInnerCount (z : Nat) : Nat := 2^(2^z-1)
def q4TerminalPrefixBlocks (z : Nat) : Nat := 2^z+z+3
def q4TerminalUnary (z : Nat) : Nat :=
  q4TerminalPrefixBlocks z + q4TerminalInnerCount z - 1
def q4TerminalRight (z : Nat) : Nat :=
  2^(q4TerminalInnerCount z-1)-1
def q4TerminalHead (z : Nat) : Int :=
  (3*2^z+3*z+7)+2+3*(q4TerminalInnerCount z)

/-- Every authentic q4Tail frame with A>=2 is already an S1 dispatcher
input, with width A+L+2 and outer index firstQ4P1M(L,A)-3. -/
theorem q4TailS0Frame_eq_generalS1Config
    (L A z : Nat) (hA : 2≤A) (hz : 1≤z) :
    q4TailS0Frame z (A+L+1) (firstQ4P1Value L A) =
      s1Config (A+L+2) (firstQ4P1M L A-3) 0
        (q4TerminalUnary z) (q4TerminalRight z) 0
        (q4TerminalHead z) := by
  let n : Nat := q4TerminalInnerCount z
  let m : Nat := 3*2^z+3*z+7
  let K : Nat := q4TerminalPrefixBlocks z
  let H : Int := m+2+3*n
  have hframe := q4TailS0Frame_eq_s0Config
    z (A+L+1) (firstQ4P1Value L A) hz
  have hres := generalEll_eq_p2Residual L A z hA
  have hK : 0<K := by dsimp [K,q4TerminalPrefixBlocks]; omega
  have hn : 0<n := by dsimp [n,q4TerminalInnerCount]; positivity
  have hconfig := generalAdapterConfig_eq L A K n H hA hK hn
  calc
    q4TailS0Frame z (A+L+1) (firstQ4P1Value L A)
        = s0Config
            (p2ResidualLeft m
              (q4TailS0Tail (A+L+1) (firstQ4P1Value L A)))
            (n-1) (2^(n-1)-1) 0 H := by
              simpa [n,m,H,q4TerminalInnerCount] using hframe
    _ = s0Config (generalEll L A K) (n-1) (2^(n-1)-1) 0 H := by
          simpa [m,K,q4TerminalPrefixBlocks] using hres
    _ = s1Config (A+L+2) (firstQ4P1M L A-3) 0
          (K+n-1) (2^(n-1)-1) 0 H :=
          generalAdapterConfig_eq L A K n H hA hK hn

#print axioms q4TailS0Frame_eq_generalS1Config

end BB6Coverage.Agent44GeneralQ4TailReparam
