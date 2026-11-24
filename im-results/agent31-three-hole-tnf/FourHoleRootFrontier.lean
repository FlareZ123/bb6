import RootFrontierR1R4
import FourHoleData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31FourHoleFrontier

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50RootFrontier BB6.Agent47RootedTNF BB6.Agent31FourHole

/-- The exact 395-bound certificate is rooted at the authentic seven-edge
    first-hole descendant of firstOneCylinder. -/
theorem wideCertificate_root :
    WeightedTNFCertificate 395 (pathEnd root 2 (path.take 7)).1 6 := by
  simpa [wideParent] using certificate

/-- Every incoming halt sibling on the seven-edge authentic path is also
    below the same local bound 395. -/
theorem path_prefix_checked :
    pathOKB 395 root 2 (path.take 7) = true := by
  decide

/-- A root-to-subtree frontier: all 23 off-path ordinary instructions are
    retained at each of the seven first-hole expansions, and the final
    four-hole cylinder is closed by its complete weighted certificate. -/
def rootFrontier : RootedFrontier 395 root :=
  buildFrontierB 395 root 2 RawRootPath.root (path.take 7)
    path_prefix_checked wideCertificate_root

theorem rootFrontier_sound :
    ∀ m, compatible root m →
      WeightedBound 395 m ∨
        ∃ address q, OpenLeaf rootFrontier address q ∧ compatible q m :=
  RootedFrontier.sound rootFrontier

theorem rootFrontier_openLeaves_disjoint :
    ∀ address1 q1 address2 q2,
      OpenLeaf rootFrontier address1 q1 →
      OpenLeaf rootFrontier address2 q2 →
      (address1, q1) ≠ (address2, q2) →
      ∀ m, ¬ (compatible q1 m ∧ compatible q2 m) :=
  RootedFrontier.openLeaves_disjoint rootFrontier

theorem rootFrontier_expanded_nodes :
    expandedNodes rootFrontier = 7 := by decide

theorem rootFrontier_closed_leaves :
    closedLeaves rootFrontier = 1 := by decide

theorem rootFrontier_residual_count :
    (residuals rootFrontier).length = 161 := by decide

#print axioms rootFrontier_sound
#print axioms rootFrontier_openLeaves_disjoint
#print axioms rootFrontier_expanded_nodes
#print axioms rootFrontier_closed_leaves
#print axioms rootFrontier_residual_count

end BB6.Agent31FourHoleFrontier
