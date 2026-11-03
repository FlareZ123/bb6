import A110Portal
import CryptidTriplePairs
import Lean.Elab.Tactic.Omega

namespace BB6.CryptidBridge

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem a_110_triple_pairs_return (m q : Nat) (ys : List Bool) :
    CryptidBoundary.run (2*m+24+6*q)
      (CryptidBoundary.preA m
        ([true,true,false] ++
          (CryptidBoundary.pairs q ++ ([true,true,true] ++ ys)))) =
    ⟨[], false,
      List.replicate (2*m+5) true ++
        (CryptidBoundary.oppairs (q+2) ++ (false::ys)), 5⟩ := by
  have ht : 2*m+24+6*q = 3+(2*(m+1)+6*q+19) := by omega
  rw [ht, CryptidBoundary.run_add, a110_to_E]
  change CryptidBoundary.run (2*(m+1)+6*q+19)
      (CryptidBoundary.eTriplePairs (m+1) q ys) = _
  rw [CryptidBoundary.eTriplePairs_run]
  rw [show 2*(m+1)+3 = 2*m+5 by omega]

#print axioms a_110_triple_pairs_return
end BB6.CryptidBridge
