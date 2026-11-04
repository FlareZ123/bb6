import Lean.Elab.Tactic.Omega
import E1101010111ThenB
import CryptidTriplePairs

namespace BB6.Agent37EThenE
open CryptidBoundary
open BB6.Agent26E1101010111
open BB6.Agent26EThenB

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- The E output with k=3t+1 is an E triple-one input; the trailing
    zero in the changed packet remains present for arbitrary suffixes. -/
theorem e_to_e_section (t q : Nat) (ys : List Bool) :
    (⟨[], false, List.replicate (8*(3*t+1)+5) true ++ bWord q ys,5⟩ : Cfg) =
    init (List.replicate (3*(8*t+3)+2) true ++
       false :: ([true,true,true] ++ (List.replicate (2*q+3) true ++ tail ys))) := by
  rw [bWord_shape]
  have hL : List.replicate (8*(3*t+1)+5) true =
      true :: true :: List.replicate (3*(8*t+3)+2) true := by
    have hn : 8*(3*t+1)+5 = 2 + (3*(8*t+3)+2) := by omega
    rw [hn]
    simpa only [List.replicate_append_replicate] using
      (show List.replicate 2 true ++ List.replicate (3*(8*t+3)+2) true =
        true :: true :: List.replicate (3*(8*t+3)+2) true by rfl)
  have hR : List.replicate (2*q+6) true =
      [true,true,true] ++ List.replicate (2*q+3) true := by
    have hn : 2*q+6 = 3 + (2*q+3) := by omega
    rw [hn]
    simpa only [List.replicate_append_replicate] using
      (show List.replicate 3 true ++ List.replicate (2*q+3) true =
        [true,true,true] ++ List.replicate (2*q+3) true by rfl)
  rw [hL,hR]
  simp [init,List.append_assoc]

/-- Exact two-return theorem against source-original transitions; applies
    to all t,q and arbitrary physical suffix without any padding erasure. -/
theorem e_then_e_raw (t q : Nat) (ys : List Bool) :
    run ((12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q) +
         (12*(8*t+3)*(8*t+3)+49*(8*t+3)+58))
      (init (List.replicate (3*(3*t+1)+2) true ++
        false :: (pairs q ++ wordE ys))) =
      ⟨[],false, List.replicate (8*(8*t+3)+9) true ++
        (oppairs 2 ++ (false :: List.replicate (2*q+3) true ++ tail ys)),5⟩ := by
  rw [run_add, full_E_1101010111_pairs (3*t+1) q ys]
  rw [e_to_e_section]
  simpa [pairs] using
    (full_E_triple_pairs (8*t+3) 0
      (List.replicate (2*q+3) true ++ tail ys))

#print axioms e_to_e_section
#print axioms e_then_e_raw
end BB6.Agent37EThenE
