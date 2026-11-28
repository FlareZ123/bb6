import D3LocalPumps

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.D3F0
open BB6Coverage Agent31Pump D3Affine

/-- All lengths, not merely the original 9 mod 4 family:
    10100·1^k -> 10100·1^(k+4) in 12k+35 moves.
    The two unbounded sweeps transfer a single 1 in 5 and 7 moves. -/
def cert (entry k : Nat) : Auto.Cert :=
  ⟨entry,⟨0,.lit [],.periodic [true,false,true,false,false] [true] (.lit (List.replicate k true))⟩,4,
    List.replicate 3 .step ++
    [.right [true] [false,false] [true] [true] (.lit [true,true,true]) (.lit (List.replicate k true)) 5] ++
    List.replicate (5*k+4) .step ++
    [.left (List.replicate (3+k) true) [true] [true] [true] (.lit [true,true,true]) (.lit []) 7] ++
    List.replicate (7*(k+3)+7) .step,12,12*k+35⟩

def v0LA : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,false,0⟩) else p0 s
theorem checked_v0LA : Auto.check v0LA (cert 96 6) = true := by decide
theorem never_v0LA (m : Machine) (hm : compatible v0LA m) : NeverHalts m := Auto.check_never v0LA (cert 96 6) checked_v0LA m hm
#print axioms never_v0LA

def v0LB : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,false,1⟩) else p0 s
theorem checked_v0LB : Auto.check v0LB (cert 55 5) = true := by decide
theorem never_v0LB (m : Machine) (hm : compatible v0LB m) : NeverHalts m := Auto.check_never v0LB (cert 55 5) checked_v0LB m hm
#print axioms never_v0LB

def v0LC : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,false,2⟩) else p0 s
theorem checked_v0LC : Auto.check v0LC (cert 43 3) = true := by decide
theorem never_v0LC (m : Machine) (hm : compatible v0LC m) : NeverHalts m := Auto.check_never v0LC (cert 43 3) checked_v0LC m hm
#print axioms never_v0LC

def v0LD : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,false,3⟩) else p0 s
theorem checked_v0LD : Auto.check v0LD (cert 49 4) = true := by decide
theorem never_v0LD (m : Machine) (hm : compatible v0LD m) : NeverHalts m := Auto.check_never v0LD (cert 49 4) checked_v0LD m hm
#print axioms never_v0LD

def v0RA : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,true,0⟩) else p0 s
theorem checked_v0RA : Auto.check v0RA (cert 118 9) = true := by decide
theorem never_v0RA (m : Machine) (hm : compatible v0RA m) : NeverHalts m := Auto.check_never v0RA (cert 118 9) checked_v0RA m hm
#print axioms never_v0RA

def v0RB : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,true,1⟩) else p0 s
theorem checked_v0RB : Auto.check v0RB (cert 112 8) = true := by decide
theorem never_v0RB (m : Machine) (hm : compatible v0RB m) : NeverHalts m := Auto.check_never v0RB (cert 112 8) checked_v0RB m hm
#print axioms never_v0RB

def v0RC : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,true,2⟩) else p0 s
theorem checked_v0RC : Auto.check v0RC (cert 71 7) = true := by decide
theorem never_v0RC (m : Machine) (hm : compatible v0RC m) : NeverHalts m := Auto.check_never v0RC (cert 71 7) checked_v0RC m hm
#print axioms never_v0RC

def v0RD : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,true,3⟩) else p0 s
theorem checked_v0RD : Auto.check v0RD (cert 91 9) = true := by decide
theorem never_v0RD (m : Machine) (hm : compatible v0RD m) : NeverHalts m := Auto.check_never v0RD (cert 91 9) checked_v0RD m hm
#print axioms never_v0RD

def v0RE : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨false,true,4⟩) else p0 s
theorem checked_v0RE : Auto.check v0RE (cert 118 9) = true := by decide
theorem never_v0RE (m : Machine) (hm : compatible v0RE m) : NeverHalts m := Auto.check_never v0RE (cert 118 9) checked_v0RE m hm
#print axioms never_v0RE

def v1LA : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨true,false,0⟩) else p0 s
theorem checked_v1LA : Auto.check v1LA (cert 37 3) = true := by decide
theorem never_v1LA (m : Machine) (hm : compatible v1LA m) : NeverHalts m := Auto.check_never v1LA (cert 37 3) checked_v1LA m hm
#print axioms never_v1LA

def v1LC : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨true,false,2⟩) else p0 s
theorem checked_v1LC : Auto.check v1LC (cert 55 4) = true := by decide
theorem never_v1LC (m : Machine) (hm : compatible v1LC m) : NeverHalts m := Auto.check_never v1LC (cert 55 4) checked_v1LC m hm
#print axioms never_v1LC

def v1LD : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨true,false,3⟩) else p0 s
theorem checked_v1LD : Auto.check v1LD (cert 65 6) = true := by decide
theorem never_v1LD (m : Machine) (hm : compatible v1LD m) : NeverHalts m := Auto.check_never v1LD (cert 65 6) checked_v1LD m hm
#print axioms never_v1LD

def v1RA : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨true,true,0⟩) else p0 s
theorem checked_v1RA : Auto.check v1RA (cert 61 6) = true := by decide
theorem never_v1RA (m : Machine) (hm : compatible v1RA m) : NeverHalts m := Auto.check_never v1RA (cert 61 6) checked_v1RA m hm
#print axioms never_v1RA

def v1RB : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨true,true,1⟩) else p0 s
theorem checked_v1RB : Auto.check v1RB (cert 53 5) = true := by decide
theorem never_v1RB (m : Machine) (hm : compatible v1RB m) : NeverHalts m := Auto.check_never v1RB (cert 53 5) checked_v1RB m hm
#print axioms never_v1RB

def v1RC : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨true,true,2⟩) else p0 s
theorem checked_v1RC : Auto.check v1RC (cert 45 4) = true := by decide
theorem never_v1RC (m : Machine) (hm : compatible v1RC m) : NeverHalts m := Auto.check_never v1RC (cert 45 4) checked_v1RC m hm
#print axioms never_v1RC

def v1RE : PartialMachine := fun s => if s = ((5 : Fin 6),false) then some (some ⟨true,true,4⟩) else p0 s
theorem checked_v1RE : Auto.check v1RE (cert 61 6) = true := by decide
theorem never_v1RE (m : Machine) (hm : compatible v1RE m) : NeverHalts m := Auto.check_never v1RE (cert 61 6) checked_v1RE m hm
#print axioms never_v1RE

end BB6Coverage.Agent31Pump.D3F0
