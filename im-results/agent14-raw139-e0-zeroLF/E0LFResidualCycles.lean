import FastFAR
import SideCycle

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent14E0LFResidualCycles
open BB6Coverage BB6Coverage.Agent50SideCycle

def p3864 : PartialMachine := FAR.fromCodes [7,10,11,22,14,17,24,16,20,11,3,0]
def p4344 : PartialMachine := FAR.fromCodes [7,12,11,24,14,21,23,16,20,11,3,13]
def p11287 : PartialMachine := FAR.fromCodes [7,8,11,3,14,21,24,16,20,11,19,2]

theorem never3864 (m : Machine) (hm : compatible p3864 m) : NeverHalts m :=
  fastSideCycleCheck_sound p3864 1443 672 false (-2) (by decide) (by decide) m hm

theorem never4344 (m : Machine) (hm : compatible p4344 m) : NeverHalts m :=
  fastSideCycleCheck_sound p4344 5234 1112 false (-8) (by decide) (by decide) m hm

theorem never11287 (m : Machine) (hm : compatible p11287 m) : NeverHalts m :=
  fastSideCycleCheck_sound p11287 2656 948 true (-7) (by decide) (by decide) m hm

#print axioms never3864
#print axioms never4344
#print axioms never11287
end BB6.Agent14E0LFResidualCycles
