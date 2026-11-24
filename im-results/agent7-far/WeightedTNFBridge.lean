import FastFAR
import WeightedTNFCertificate

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- Import a checked finite-automata nonhalting certificate into the
    existing sparse-TNF Cover interface. -/
theorem farNonhaltCover (p : PartialMachine) (limit : Nat)
    (h : FAR.fastOracle p limit = true) : Cover NeverHalts p :=
  .leaf p (fun m hm => FAR.fastOracle_sound p limit h m hm)

/-- A FAR certificate closes a normalized TNF node without any score
    calculation: nonhalting is automatically safe for every target B. -/
def farNonhaltLeaf {B : Nat} {p : PartialMachine} {cut : Nat}
    (hroot : p initialSlot = some (some ⟨true, true, 1⟩))
    (hsupport : TNFSupport p cut)
    (hnohalt : weightedTNFNoAssignedHalt p)
    (limit : Nat) (h : FAR.fastOracle p limit = true) :
    WeightedTNFCertificate B p cut :=
  WeightedTNFCertificate.ofNonhaltCover hroot hsupport hnohalt
    (farNonhaltCover p limit h)

#print axioms farNonhaltCover
#print axioms farNonhaltLeaf
end BB6.Agent13BlankDelay
