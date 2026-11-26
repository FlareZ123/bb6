import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M15
-- 1RB0LF_1RC---_0RD0RB_1LD1RE_0RC0LF_1RC0LA

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[true,true,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false] ++ rep [false,false,false,false,true,false,true,false,false,false,true,false] n ++ [true,false,true,false,true,false,true,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,false,false,true]⟩

def entryC0 : Z0 := ⟨0,[],[]⟩

def entryC1 : Z0 := ⟨1,[false,false,true,false,false,true,false,true,true],[false,false,true,false,true,false,false,false,true,true,false,false,false,true]⟩

def entryC2 : Z0 := ⟨3,[true,true,true,false,true,false,true,false,true,false,false,true,false,true,true],[true,true,false,false,false,false,false,true,false,false,true,false,false,true]⟩

def entryC3 : Z0 := ⟨5,[true,true,true,true,false,true,false,true,true,true,true,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true],[false,true]⟩

def entryC4 : Z0 := ⟨5,[true,false,false,true,false,true,true],[false,false,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,false,false,false,false,true,false,true,false,false,false,true]⟩

def entryC5 : Z0 := ⟨0,[false,true,false,true,false,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true],[false,false,false,false,true,false,false,false,true,false,false,false,false,true,false,true,false,false,false,true]⟩

def entryC6 : Z0 := ⟨3,[false,true,true,true,false,false,true,false,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true,false,true,true],[true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC7 : Z0 := ⟨1,[false,false,false,true,false,true,true],[true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC8 : Z0 := ⟨0,[true],[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,false,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC9 : Z0 := ⟨3,[false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true],[true,false,true,false,true,false,false,false,true,false,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC10 : Z0 := ⟨1,[false,true,true,false,true,false,true,false,true,false,false,true,false,true,true],[false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC11 : Z0 := ⟨3,[false,true,true,true,false,true,false,true,false,false,true,false,true,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC12 : Z0 := ⟨3,[false,false,true,true,true,false,true,false,true,false,true,false,false,true,false,true,true],[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC13 : Z0 := ⟨0,[true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true],[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC14 : Z0 := ⟨5,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true],[false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC15 : Z0 := ⟨3,[true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true],[true,true,true,false,false,true,false,true,false,false,false,true]⟩

def entryC16 : Z0 := ⟨5,[false,false,true,false,true,true],[false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC17 : Z0 := ⟨4,[true,true,true,false,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[true,false,true,false,true,false,false,false,false,false,true,false,true,false,false,false,true]⟩

def entryC18 : Z0 := ⟨5,[true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[false,true,false,true,false,true,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC19 : Z0 := ⟨0,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,true],[false,false,false,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC20 : Z0 := ⟨3,[true,true],[true,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC21 : Z0 := ⟨3,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true],[true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC22 : Z0 := ⟨5,[true,true,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true],[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,true,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC23 : Z0 := ⟨3,[false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,false,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,true,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,false,true,false,true,false,false,false,true]⟩

def entryC24 : Z0 := ⟨3,[false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC25 : Z0 := ⟨1,[false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[false,false,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC26 : Z0 := ⟨2,[true,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,true],[false,false,false,true,false,false,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC27 : Z0 := ⟨0,[true,false,true,true],[false,false,true,false,true,false,true,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC28 : Z0 := ⟨5,[false,true,true,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true],[false,false,false,true,false,true,false,true,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC29 : Z0 := ⟨2,[true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,true,true,true,true,true,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[false,false,false,false,false,true,false,false,false,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC30 : Z0 := ⟨2,[false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,true,true,true,true,true,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[false,false,false,false,true,true,false,false,false,true,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC31 : Z0 := ⟨3,[true,true,false,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[true,true,false,false,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,true,false,false,false,true,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC32 : Z0 := ⟨5,[true,true,true],[false,true,false,true,false,true,false,false,false,true,false,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,false,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,true,false,false,false,true,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC33 : Z0 := ⟨2,[true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true],[false,true,false,true,false,false,false,true,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,false,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,true,false,false,false,true,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC34 : Z0 := ⟨4,[true,true,true,false,false,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[true,false,true,false,true,false,true,false,false,false,true,true,false,false,false,true,false,true,false,true,false,false,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,true,true,false,false,false,true,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true]⟩

def entryC35 : Z0 := ⟨5,[false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false,true,true,true,true,true,true,true,true,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[false,false,false,false,false,true]⟩

def entryC36 : Z0 := ⟨3,[false,false,true,true,true,true,false,false,true,false,true,true,true,true,true,true,true,true,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[false,true,false,true,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,false,false,true]⟩

def entryC37 : Z0 := family 0

def growthC0 (n : Nat) : Z0 := family n

def growthC1 (n : Nat) : Z0 := ⟨3,[false,true,true,true],[true,false,false,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false] ++ rep [false,false,false,false,true,false,true,false,false,false,true,false] n ++ [true,false,true,false,true,false,true,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,false,false,true]⟩

def growthC2 (n : Nat) : Z0 := ⟨5,[true,false,true,false,true,false,false,true,false,true,true],[false,false,false,true,false,true,false,false,false,true,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false] ++ rep [false,false,false,false,true,false,true,false,false,false,true,false] n ++ [true,false,true,false,true,false,true,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,false,false,true]⟩

def growthC3 (n : Nat) : Z0 := ⟨3,[false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[true,false,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false] ++ rep [false,false,false,false,true,false,true,false,false,false,true,false] n ++ [true,false,true,false,true,false,true,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,false,false,true]⟩

def growthC4 (n : Nat) : Z0 := ⟨3,[false,false,true,false,true,false,true,true,true,true,true,true,true,true,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,true,false,true,true],[false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,false] ++ rep [false,false,false,false,true,false,true,false,false,false,true,false] n ++ [true,false,true,false,true,false,true,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,false,false,true]⟩

def growthC5 (n : Nat) : Z0 := family (n+1)
end M15
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
