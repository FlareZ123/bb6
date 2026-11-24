import Cryptids608NonHalt
import WeightedNonhaltLeafAdapter

set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

namespace BB6.Agent47WeightedHalt.Cryptids

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Cryptids608
open BB6.Agent47WeightedHalt

/-- Each pinned Cryptids nonhalt proof can be imported as a weighted-TNF
    leaf after erasing its unreachable halt row(s). The canonical completion
    of the erased table is the original complete machine. -/

theorem r1_weighted_leaf (B : Nat) :
    WeightedTNFCertificate B (forgetHaltRows expectedRLE_r1) 6 := by
  apply forgetHaltRows_nonhaltCertificate
  · simp [expectedRLE_r1, initialSlot]
  · exact literal_r1_never

theorem r2_weighted_leaf (B : Nat) :
    WeightedTNFCertificate B (forgetHaltRows expectedRLE_r2) 6 := by
  apply forgetHaltRows_nonhaltCertificate
  · simp [expectedRLE_r2, initialSlot]
  · exact literal_r2_never

theorem r3_weighted_leaf (B : Nat) :
    WeightedTNFCertificate B (forgetHaltRows expectedRLE_r3) 6 := by
  apply forgetHaltRows_nonhaltCertificate
  · simp [expectedRLE_r3, initialSlot]
  · exact literal_r3_never

theorem r4_weighted_leaf (B : Nat) :
    WeightedTNFCertificate B (forgetHaltRows expectedRLE_r4) 6 := by
  apply forgetHaltRows_nonhaltCertificate
  · simp [expectedRLE_r4, initialSlot]
  · exact literal_r4_never

theorem r5_weighted_leaf (B : Nat) :
    WeightedTNFCertificate B (forgetHaltRows expectedRLE_r5) 6 := by
  apply forgetHaltRows_nonhaltCertificate
  · simp [expectedRLE_r5, initialSlot]
  · exact literal_r5_never

theorem r6_weighted_leaf (B : Nat) :
    WeightedTNFCertificate B (forgetHaltRows expectedRLE_r6) 6 := by
  apply forgetHaltRows_nonhaltCertificate
  · simp [expectedRLE_r6, initialSlot]
  · exact literal_r6_never

theorem r1_weighted_cover (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows expectedRLE_r1) :=
  WeightedTNFCertificate.sound (r1_weighted_leaf B)

theorem r2_weighted_cover (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows expectedRLE_r2) :=
  WeightedTNFCertificate.sound (r2_weighted_leaf B)

theorem r3_weighted_cover (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows expectedRLE_r3) :=
  WeightedTNFCertificate.sound (r3_weighted_leaf B)

theorem r4_weighted_cover (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows expectedRLE_r4) :=
  WeightedTNFCertificate.sound (r4_weighted_leaf B)

theorem r5_weighted_cover (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows expectedRLE_r5) :=
  WeightedTNFCertificate.sound (r5_weighted_leaf B)

theorem r6_weighted_cover (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows expectedRLE_r6) :=
  WeightedTNFCertificate.sound (r6_weighted_leaf B)

#print axioms r1_weighted_leaf
#print axioms r2_weighted_leaf
#print axioms r3_weighted_leaf
#print axioms r4_weighted_leaf
#print axioms r5_weighted_leaf
#print axioms r6_weighted_leaf
#print axioms r1_weighted_cover
#print axioms r2_weighted_cover
#print axioms r3_weighted_cover
#print axioms r4_weighted_cover
#print axioms r5_weighted_cover
#print axioms r6_weighted_cover

end BB6.Agent47WeightedHalt.Cryptids
