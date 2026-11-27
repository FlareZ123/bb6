import Raw420RBClosedRoot_16_17_12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw420RB.Closed
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent32PartialCut BB6.Agent32PackedClosed BB6.Agent32Raw59QuickWeight

theorem recovered_16_17_12_cover : Cover (WeightedBound 1006) pRoot_16_17_12 :=
  closedCover 1006 6 pRoot_16_17_12 tRoot_16_17_12 (by decide)
    (support6 _) (by decide) (by
      apply weightedTNFNoAssignedHalt_refine
      apply weightedTNFNoAssignedHalt_refine
      apply weightedTNFNoAssignedHalt_refine
      apply weightedTNFNoAssignedHalt_refine
      exact BB6.Agent32Raw42.parent_nohalt) cRoot_16_17_12
#print axioms recovered_16_17_12_cover
end BB6.Agent32Raw420RB.Closed
