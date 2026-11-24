import FARCheck
namespace BB6Coverage.FAR
set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- A/0=0RB, A/1=1LA, B/0=1LA, B/1=1RB. Other rows unassigned.
abbrev exampleTable := fromCodes [5,2,2,7,24,24,24,24,24,24,24,24]
def exampleCert : Data 1 := ⟨0,[0,0],[2,2,64,64,64,64,64],[2,2,64,64,64,64,64],124⟩
theorem exampleNever (m : Machine) (hm : compatible exampleTable m) : NeverHalts m :=
  exampleCert.sound exampleTable (by decide) m hm
#print axioms exampleNever
end BB6Coverage.FAR
