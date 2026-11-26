import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M90
-- 1RB---_1RC1RB_0RD0RA_1LD1RE_0LE0LF_1LB1LE

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true] ++ rep [false,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,false,true,true,true,false,true,true] n ++ [true,false,true,true,false,true,true,false,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩

def entryC0 : Z0 := ⟨0,[],[]⟩

def entryC1 : Z0 := ⟨1,[true,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,false,true,true,true,false,true,true,false,true],[false,false]⟩

def entryC2 : Z0 := ⟨2,[false,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,false,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩

def entryC3 : Z0 := ⟨4,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩

def entryC4 : Z0 := family 0

def growthC0 (n : Nat) : Z0 := family n

def growthC1 (n : Nat) : Z0 := ⟨0,[false,false,true,true,true,false,true,true,true,false,true,true,false,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true] ++ rep [false,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,false,true,true,true,false,true,true] n ++ [true,false,true,true,false,true,true,false,true],[]⟩

def growthC2 (n : Nat) : Z0 := ⟨1,[false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true] ++ rep [false,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,true,true,false,true,true,true,false,true,true] n ++ [true,false,true,true,false,true,true,false,true],[false]⟩

def growthC3 (n : Nat) : Z0 := family (n+1)
end M90
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
