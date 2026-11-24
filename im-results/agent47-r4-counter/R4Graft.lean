import R4Parent
import CryptidsWeightedLeaves

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace BB6.Agent47R4Graft
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47R1Parent BB6.Agent47R4Parent BB6.Agent47WeightedHalt
open BB6.Agent47WeightedHalt.Cryptids BB6.Cryptids608

theorem r4_special_exact : r4.child r4.special = forgetHaltRows expectedRLE_r4 :=
  partialEq_sound _ _ (by decide)

def r4_certificate : WeightedTNFCertificate r4.bound r4.parent 6 :=
  assemble r4 r4_valid (by rw [r4_special_exact]; exact r4_weighted_leaf r4.bound)

theorem r4_exact_weighted_threshold (B : Nat) :
    (∀ m, compatible r4.parent m → WeightedBound B m) ↔ 42 ≤ B :=
  r4_exact_from_attained r4_certificate B

#print axioms r4_special_exact
#print axioms r4_certificate
#print axioms r4_exact_weighted_threshold
end BB6.Agent47R4Graft
