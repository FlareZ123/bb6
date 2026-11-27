import Hybrid
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent6OneLFLongCycle
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6.Agent6Hybrid
def pH10068 : PartialMachine := fromCodes [7,7,11,7,14,17,24,16,22,11,2,10]
theorem cH10068 : Cover (WeightedBound 90794) pH10068 :=
  sound 90794 pH10068 (.closed (.cycle 1905 394 true (26))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH10068

def pH10708 : PartialMachine := fromCodes [7,24,11,7,14,17,2,16,22,11,6,10]
theorem cH10708 : Cover (WeightedBound 90794) pH10708 :=
  sound 90794 pH10708 (.closed (.cycle 1606 394 true (7))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH10708

def pH12373 : PartialMachine := fromCodes [7,2,11,13,14,24,1,16,22,11,14,20]
theorem cH12373 : Cover (WeightedBound 90794) pH12373 :=
  sound 90794 pH12373 (.closed (.cycle 9498 2127 false (-49))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH12373

def pH14336_8 : PartialMachine := fromCodes [7,21,11,3,14,8,24,16,22,11,3,20]
theorem cH14336_8 : Cover (WeightedBound 90794) pH14336_8 :=
  sound 90794 pH14336_8 (.closed (.cycle 1681 564 false (-15))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH14336_8

def pH14336_13 : PartialMachine := fromCodes [7,21,11,3,14,13,24,16,22,11,3,20]
theorem cH14336_13 : Cover (WeightedBound 90794) pH14336_13 :=
  sound 90794 pH14336_13 (.closed (.cycle 1206 564 false (-5))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH14336_13

def pH14336_10 : PartialMachine := fromCodes [7,21,11,3,14,10,24,16,22,11,3,20]
theorem cH14336_10 : Cover (WeightedBound 90794) pH14336_10 :=
  sound 90794 pH14336_10 (.closed (.cycle 2919 564 false (-16))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH14336_10

def pH14875 : PartialMachine := fromCodes [7,3,11,10,14,17,24,16,22,11,3,10]
theorem cH14875 : Cover (WeightedBound 90794) pH14875 :=
  sound 90794 pH14875 (.closed (.cycle 3265 3661 true (23))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH14875

def pH14896 : PartialMachine := fromCodes [7,3,11,11,14,17,24,16,22,11,3,10]
theorem cH14896 : Cover (WeightedBound 90794) pH14896 :=
  sound 90794 pH14896 (.closed (.cycle 1086 526 true (8))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH14896

def pH15196 : PartialMachine := fromCodes [7,23,11,1,14,4,24,16,22,11,3,8]
theorem cH15196 : Cover (WeightedBound 90794) pH15196 :=
  sound 90794 pH15196 (.closed (.cycle 1745 619 false (-20))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH15196

def pH16306 : PartialMachine := fromCodes [7,24,11,7,14,17,0,16,22,11,7,10]
theorem cH16306 : Cover (WeightedBound 90794) pH16306 :=
  sound 90794 pH16306 (.closed (.cycle 886 378 true (5))) (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms cH16306

end BB6.Agent6OneLFLongCycle
