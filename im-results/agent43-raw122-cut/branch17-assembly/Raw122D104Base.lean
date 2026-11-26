import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M104
-- 1RB0LE_1RC1RA_0RD---_1LD1RE_0LA0LF_0RB1LF

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false],[false,false,false,false,false,false,false,false,false] ++ rep [false,false,false,false] n ++ [true,false,true]⟩

def entryC0 : Z0 := ⟨0,[],[]⟩

def entryC1 : Z0 := ⟨3,[true,false],[true,true,true,false,false,false,false,false,false,false,false,false,false,true,false,true]⟩

def entryC2 : Z0 := ⟨3,[false,false,true,false,true,false,true,false,true,false,true,false,true,false],[false,true,true,true,true,true,false,true]⟩

def entryC3 : Z0 := family 0

def growthC0 (n : Nat) : Z0 := family n

def growthC1 (n : Nat) : Z0 := ⟨5,[true,true,true,false,true,false,true,false,true,false,true,false],[false,true,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false] ++ rep [false,false,false,false] n ++ [true,false,true]⟩

def growthC2 (n : Nat) : Z0 := ⟨1,[false,true,true,true,true,true,true,true,true,true,true,false,true,false,true,false,true,false,true,false],[false,true,false,false,false,false,false,false,false,false,false] ++ rep [false,false,false,false] n ++ [true,false,true]⟩

def growthC3 (n : Nat) : Z0 := family (n+1)
end M104
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
