import D3LocalPumps

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.D3F0
open BB6Coverage Agent31Pump D3Affine

def v0LB : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,false,1⟩) else p0 s
def cv0LB : Auto.Cert := { c0 with entry := 150 }
theorem checked_v0LB : Auto.check v0LB cv0LB = true := by decide
theorem never_v0LB (m : Machine) (hm : compatible v0LB m) : NeverHalts m := Auto.check_never v0LB cv0LB checked_v0LB m hm
#print axioms never_v0LB

def v0RA : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,true,0⟩) else p0 s
def cv0RA : Auto.Cert := { c0 with entry := 118 }
theorem checked_v0RA : Auto.check v0RA cv0RA = true := by decide
theorem never_v0RA (m : Machine) (hm : compatible v0RA m) : NeverHalts m := Auto.check_never v0RA cv0RA checked_v0RA m hm
#print axioms never_v0RA

def v0RD : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,true,3⟩) else p0 s
def cv0RD : Auto.Cert := { c0 with entry := 91 }
theorem checked_v0RD : Auto.check v0RD cv0RD = true := by decide
theorem never_v0RD (m : Machine) (hm : compatible v0RD m) : NeverHalts m := Auto.check_never v0RD cv0RD checked_v0RD m hm
#print axioms never_v0RD

def v0RE : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,true,4⟩) else p0 s
def cv0RE : Auto.Cert := { c0 with entry := 118 }
theorem checked_v0RE : Auto.check v0RE cv0RE = true := by decide
theorem never_v0RE (m : Machine) (hm : compatible v0RE m) : NeverHalts m := Auto.check_never v0RE cv0RE checked_v0RE m hm
#print axioms never_v0RE

def v1RB : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨true,true,1⟩) else p0 s
def cv1RB : Auto.Cert := { c0 with entry := 148 }
theorem checked_v1RB : Auto.check v1RB cv1RB = true := by decide
theorem never_v1RB (m : Machine) (hm : compatible v1RB m) : NeverHalts m := Auto.check_never v1RB cv1RB checked_v1RB m hm
#print axioms never_v1RB

end BB6Coverage.Agent31Pump.D3F0
