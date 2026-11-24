import CanonicalTNFBridge
import FARWeightedTNFExample

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- Regard the explicit FAR nonhalting proof as a canonical audit leaf. -/
def gliderDecidedCover (B : Nat) :
    Cover (DecidedBelow (B - 5)) gliderExample :=
  .leaf gliderExample (fun m hm =>
    Or.inl ((farDataNonhaltCover gliderExample gliderFARData gliderFARValid).sound m hm))

def gliderCanonicalAudit (B : Nat) :
    BB6Coverage.Canonical.Audit (B - 5) gliderExample 3 :=
  .certified gliderExample 3 (gliderDecidedCover B)

theorem gliderCanonicalAudit_closed (B : Nat) :
    (gliderCanonicalAudit B).report.2 = 0 := by
  simp [gliderCanonicalAudit, BB6Coverage.Canonical.Audit.report]

/-- The canonical-audit adapter, including the five-step delay margin,
    produces a weighted-TNF certificate for the glider cylinder. -/
def gliderCanonicalTNFLeaf (B : Nat) (hB : 5 ≤ B) :
    WeightedTNFCertificate B gliderExample 3 :=
  canonicalAuditTNFLeaf hB gliderRoot gliderSupport gliderNoAssignedHalt
    (gliderCanonicalAudit B) (gliderCanonicalAudit_closed B)

theorem gliderCanonicalTNFLeaf_sound (B : Nat) (hB : 5 ≤ B) :
    ∀ m, compatible gliderExample m → WeightedBound B m :=
  (gliderCanonicalTNFLeaf B hB).sound

#print axioms gliderCanonicalTNFLeaf_sound
end BB6.Agent13BlankDelay
