import Hybrid
import PartialAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent6E0OneRELongQueries
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6Coverage.Agent10ZipAudit
def p479 : PartialMachine := fromCodes [7,14,11,21,14,5,24,16,19,11,22,2]
theorem c479 : Cover (WeightedBound 19745) p479 := by
  apply Cover.leaf
  intro m hm
  exact (certifiedZip 19745 p479 (.last 1434 (3,false)) (by decide) (BB6.Agent6Hybrid.fromCodes_nohalt _) (by decide +kernel)).sound m hm
#print axioms c479
def p897 : PartialMachine := fromCodes [7,14,11,6,14,21,24,16,19,11,2,23]
theorem c897 : Cover (WeightedBound 19745) p897 := by
  apply Cover.leaf
  intro m hm
  exact (certifiedZip 19745 p897 (.last 1007 (3,false)) (by decide) (BB6.Agent6Hybrid.fromCodes_nohalt _) (by decide +kernel)).sound m hm
#print axioms c897
def p1763 : PartialMachine := fromCodes [7,5,11,21,14,3,24,16,19,11,10,2]
theorem c1763 : Cover (WeightedBound 19745) p1763 := by
  apply Cover.leaf
  intro m hm
  exact (certifiedZip 19745 p1763 (.last 5819 (3,false)) (by decide) (BB6.Agent6Hybrid.fromCodes_nohalt _) (by decide +kernel)).sound m hm
#print axioms c1763
def p2014 : PartialMachine := fromCodes [7,21,11,14,14,3,24,16,19,11,6,23]
theorem c2014 : Cover (WeightedBound 19745) p2014 := by
  apply Cover.leaf
  intro m hm
  exact (certifiedZip 19745 p2014 (.last 19739 (3,false)) (by decide) (BB6.Agent6Hybrid.fromCodes_nohalt _) (by decide +kernel)).sound m hm
#print axioms c2014
end BB6.Agent6E0OneRELongQueries
