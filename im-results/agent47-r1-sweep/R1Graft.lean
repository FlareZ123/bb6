import R1Parent
import CryptidsWeightedLeaves

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace BB6.Agent47R1Graft
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47R1Parent BB6.Agent47WeightedHalt
open BB6.Agent47WeightedHalt.Cryptids BB6.Cryptids608

theorem r1_special_exact : r1.child r1.special = forgetHaltRows expectedRLE_r1 :=
  partialEq_sound _ _ (by decide)

def r1_certificate : WeightedTNFCertificate r1.bound r1.parent 6 :=
  assemble r1 r1_valid (by rw [r1_special_exact]; exact r1_weighted_leaf r1.bound)

theorem r1_exact_weighted_threshold (B : Nat) :
    (∀ m, compatible r1.parent m → WeightedBound B m) ↔ 7014 ≤ B :=
  exact_from_attained r1_certificate B

#print axioms r1_special_exact
#print axioms r1_certificate
#print axioms r1_exact_weighted_threshold
end BB6.Agent47R1Graft
