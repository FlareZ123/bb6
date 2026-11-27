import Raw36FirstOverflowA2

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Auto.Raw36FirstRoot
open BB6Coverage Agent31Pump Auto

def p : PartialMachine := Raw36FirstOverflowA2.p

/-- Authentic 416-step blank entry to B(9,1). -/
def rootB : PZ := ⟨1,.lit [],.lit [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,false]⟩

/-- Authentic 13244-step blank entry to A(17,52), the first
    convenient phase with mass >=121. -/
def rootA : PZ := ⟨0,.lit [],.lit [false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false]⟩

theorem root416 :
    run0 p 416 ⟨0,[],[]⟩ = some (rootB.eval 0) := by decide

theorem root13244 :
    run0 p 13244 ⟨0,[],[]⟩ = some (rootA.eval 0) := by decide

#print axioms root416
#print axioms root13244
end BB6Coverage.Agent31Pump.Auto.Raw36FirstRoot
