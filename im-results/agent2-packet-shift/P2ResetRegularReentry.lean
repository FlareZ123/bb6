import PacketP2ResetSource
import ERemaining
import Lean.Elab.Tactic.Omega

namespace BB6.P2ResetRegularReentry
open CryptidBoundary

/-- The original-source E,p=2 reset always lands directly in the canonical
    DRegular F/0 language. The specialized k-residue theorems give shorter
    later returns, but are unnecessary for basic regular reentry. -/
theorem e_two_reset_regular_reentry (k q : Nat) :
    run (12*k*k + 49*k + 68 + 4*q)
      (BB6.PacketP2ResetSource.packet (3*k+4) q 2
        (false :: List.replicate 6 true)) =
      DRegularSource.sourceSection ⟨8*k+6,3,2⟩ := by
  rw [BB6.PacketP2ResetSource.e_two_reset]
  rw [BB6.ERemaining.source_rep (8*k+6) 3 2 (by omega)]
  unfold BB6.PacketP2ResetSource.marker
  rw [← List.singleton_append]
  rw [← List.append_assoc]
  have hrep :
      List.replicate (8*k+5) true ++ [true] =
        List.replicate (8*k+6) true := by
    simpa using
      (List.replicate_append_replicate (n:=8*k+5) (m:=1) (a:=true))
  rw [hrep]

end BB6.P2ResetRegularReentry
