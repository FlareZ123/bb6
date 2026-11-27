import ZipThreeHoleAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6D1TwoLate163
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot

def p : PartialMachine := FAR.fromCodes [7,0,11,16,14,19,2,13,22,9,24,18]
abbrev z0 : Z := start
def z500 : Z := ⟨2,4,[false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true]⟩
def z1000 : Z := ⟨3,4,[true,false,false,false,true,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z1500 : Z := ⟨2,18,[false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,false,true,true]⟩
def z2000 : Z := ⟨2,16,[false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z2500 : Z := ⟨1,14,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z3000 : Z := ⟨2,-2,[false,false,true,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z3500 : Z := ⟨2,-4,[false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z4000 : Z := ⟨3,34,[false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true]⟩
def z4500 : Z := ⟨3,26,[false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z5000 : Z := ⟨4,24,[true,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z5500 : Z := ⟨3,30,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z6000 : Z := ⟨3,16,[true,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z6500 : Z := ⟨4,18,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z7000 : Z := ⟨2,46,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true]⟩
def z7500 : Z := ⟨3,14,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z8000 : Z := ⟨3,42,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z8500 : Z := ⟨3,42,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z9000 : Z := ⟨2,26,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z9500 : Z := ⟨3,12,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z10000 : Z := ⟨0,52,[false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z10500 : Z := ⟨4,62,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[false,true,true,true,true,true,true,true,true]⟩
def z11000 : Z := ⟨0,38,[true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z11500 : Z := ⟨3,54,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z12000 : Z := ⟨0,34,[false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z12500 : Z := ⟨4,54,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z13000 : Z := ⟨3,44,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z13500 : Z := ⟨0,60,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z14000 : Z := ⟨0,36,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z14500 : Z := ⟨0,14,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z15000 : Z := ⟨3,84,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true]⟩
def z15500 : Z := ⟨0,76,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true]⟩
def z16000 : Z := ⟨0,70,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z16500 : Z := ⟨4,68,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z17000 : Z := ⟨1,70,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z17500 : Z := ⟨4,74,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z18000 : Z := ⟨0,82,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true]⟩
def z18500 : Z := ⟨3,84,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true]⟩
def z19000 : Z := ⟨3,12,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z19500 : Z := ⟨4,10,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z20000 : Z := ⟨1,30,[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z20500 : Z := ⟨4,52,[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,true,true],[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z21000 : Z := ⟨0,78,[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z21500 : Z := ⟨4,16,[true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
def z21697 : Z := ⟨5,-17,[],[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]⟩
theorem segment500 : zrun p 500 z0 = some z500 := by rfl
theorem segment1000 : zrun p 500 z500 = some z1000 := by rfl
theorem segment1500 : zrun p 500 z1000 = some z1500 := by rfl
theorem segment2000 : zrun p 500 z1500 = some z2000 := by rfl
theorem segment2500 : zrun p 500 z2000 = some z2500 := by rfl
theorem segment3000 : zrun p 500 z2500 = some z3000 := by rfl
theorem segment3500 : zrun p 500 z3000 = some z3500 := by rfl
theorem segment4000 : zrun p 500 z3500 = some z4000 := by rfl
theorem segment4500 : zrun p 500 z4000 = some z4500 := by rfl
theorem segment5000 : zrun p 500 z4500 = some z5000 := by rfl
theorem segment5500 : zrun p 500 z5000 = some z5500 := by rfl
theorem segment6000 : zrun p 500 z5500 = some z6000 := by rfl
theorem segment6500 : zrun p 500 z6000 = some z6500 := by rfl
theorem segment7000 : zrun p 500 z6500 = some z7000 := by rfl
theorem segment7500 : zrun p 500 z7000 = some z7500 := by rfl
theorem segment8000 : zrun p 500 z7500 = some z8000 := by rfl
theorem segment8500 : zrun p 500 z8000 = some z8500 := by rfl
theorem segment9000 : zrun p 500 z8500 = some z9000 := by rfl
theorem segment9500 : zrun p 500 z9000 = some z9500 := by rfl
theorem segment10000 : zrun p 500 z9500 = some z10000 := by rfl
theorem segment10500 : zrun p 500 z10000 = some z10500 := by rfl
theorem segment11000 : zrun p 500 z10500 = some z11000 := by rfl
theorem segment11500 : zrun p 500 z11000 = some z11500 := by rfl
theorem segment12000 : zrun p 500 z11500 = some z12000 := by rfl
theorem segment12500 : zrun p 500 z12000 = some z12500 := by rfl
theorem segment13000 : zrun p 500 z12500 = some z13000 := by rfl
theorem segment13500 : zrun p 500 z13000 = some z13500 := by rfl
theorem segment14000 : zrun p 500 z13500 = some z14000 := by rfl
theorem segment14500 : zrun p 500 z14000 = some z14500 := by rfl
theorem segment15000 : zrun p 500 z14500 = some z15000 := by rfl
theorem segment15500 : zrun p 500 z15000 = some z15500 := by rfl
theorem segment16000 : zrun p 500 z15500 = some z16000 := by rfl
theorem segment16500 : zrun p 500 z16000 = some z16500 := by rfl
theorem segment17000 : zrun p 500 z16500 = some z17000 := by rfl
theorem segment17500 : zrun p 500 z17000 = some z17500 := by rfl
theorem segment18000 : zrun p 500 z17500 = some z18000 := by rfl
theorem segment18500 : zrun p 500 z18000 = some z18500 := by rfl
theorem segment19000 : zrun p 500 z18500 = some z19000 := by rfl
theorem segment19500 : zrun p 500 z19000 = some z19500 := by rfl
theorem segment20000 : zrun p 500 z19500 = some z20000 := by rfl
theorem segment20500 : zrun p 500 z20000 = some z20500 := by rfl
theorem segment21000 : zrun p 500 z20500 = some z21000 := by rfl
theorem segment21500 : zrun p 500 z21000 = some z21500 := by rfl
theorem segment21697 : zrun p 197 z21500 = some z21697 := by rfl
theorem prefix500 : zrun p 500 start = some z500 := segment500
theorem prefix1000 : zrun p 1000 start = some z1000 := join prefix500 segment1000
theorem prefix1500 : zrun p 1500 start = some z1500 := join prefix1000 segment1500
theorem prefix2000 : zrun p 2000 start = some z2000 := join prefix1500 segment2000
theorem prefix2500 : zrun p 2500 start = some z2500 := join prefix2000 segment2500
theorem prefix3000 : zrun p 3000 start = some z3000 := join prefix2500 segment3000
theorem prefix3500 : zrun p 3500 start = some z3500 := join prefix3000 segment3500
theorem prefix4000 : zrun p 4000 start = some z4000 := join prefix3500 segment4000
theorem prefix4500 : zrun p 4500 start = some z4500 := join prefix4000 segment4500
theorem prefix5000 : zrun p 5000 start = some z5000 := join prefix4500 segment5000
theorem prefix5500 : zrun p 5500 start = some z5500 := join prefix5000 segment5500
theorem prefix6000 : zrun p 6000 start = some z6000 := join prefix5500 segment6000
theorem prefix6500 : zrun p 6500 start = some z6500 := join prefix6000 segment6500
theorem prefix7000 : zrun p 7000 start = some z7000 := join prefix6500 segment7000
theorem prefix7500 : zrun p 7500 start = some z7500 := join prefix7000 segment7500
theorem prefix8000 : zrun p 8000 start = some z8000 := join prefix7500 segment8000
theorem prefix8500 : zrun p 8500 start = some z8500 := join prefix8000 segment8500
theorem prefix9000 : zrun p 9000 start = some z9000 := join prefix8500 segment9000
theorem prefix9500 : zrun p 9500 start = some z9500 := join prefix9000 segment9500
theorem prefix10000 : zrun p 10000 start = some z10000 := join prefix9500 segment10000
theorem prefix10500 : zrun p 10500 start = some z10500 := join prefix10000 segment10500
theorem prefix11000 : zrun p 11000 start = some z11000 := join prefix10500 segment11000
theorem prefix11500 : zrun p 11500 start = some z11500 := join prefix11000 segment11500
theorem prefix12000 : zrun p 12000 start = some z12000 := join prefix11500 segment12000
theorem prefix12500 : zrun p 12500 start = some z12500 := join prefix12000 segment12500
theorem prefix13000 : zrun p 13000 start = some z13000 := join prefix12500 segment13000
theorem prefix13500 : zrun p 13500 start = some z13500 := join prefix13000 segment13500
theorem prefix14000 : zrun p 14000 start = some z14000 := join prefix13500 segment14000
theorem prefix14500 : zrun p 14500 start = some z14500 := join prefix14000 segment14500
theorem prefix15000 : zrun p 15000 start = some z15000 := join prefix14500 segment15000
theorem prefix15500 : zrun p 15500 start = some z15500 := join prefix15000 segment15500
theorem prefix16000 : zrun p 16000 start = some z16000 := join prefix15500 segment16000
theorem prefix16500 : zrun p 16500 start = some z16500 := join prefix16000 segment16500
theorem prefix17000 : zrun p 17000 start = some z17000 := join prefix16500 segment17000
theorem prefix17500 : zrun p 17500 start = some z17500 := join prefix17000 segment17500
theorem prefix18000 : zrun p 18000 start = some z18000 := join prefix17500 segment18000
theorem prefix18500 : zrun p 18500 start = some z18500 := join prefix18000 segment18500
theorem prefix19000 : zrun p 19000 start = some z19000 := join prefix18500 segment19000
theorem prefix19500 : zrun p 19500 start = some z19500 := join prefix19000 segment19500
theorem prefix20000 : zrun p 20000 start = some z20000 := join prefix19500 segment20000
theorem prefix20500 : zrun p 20500 start = some z20500 := join prefix20000 segment20500
theorem prefix21000 : zrun p 21000 start = some z21000 := join prefix20500 segment21000
theorem prefix21500 : zrun p 21500 start = some z21500 := join prefix21000 segment21500
theorem prefix21697 : zrun p 21697 start = some z21697 := join prefix21500 segment21697

theorem known : knownRun p 21697 = some (embed z21697) := by
  rw [knownRun_zip,prefix21697]
  rfl

theorem cover : Cover (WeightedBound 21698) p :=
  .leaf _ (WeightedTNFCertificate.lastHole (cut := 6) (by decide) (support6 p) (by decide)
    known (by decide) (restOK_sound p (readSlot (embed z21697)) (by decide))
    (weightOK_sound p (readSlot (embed z21697)) 21697 21698 (by decide))).sound
#print axioms cover
end BB6.Agent6D1TwoLate163
