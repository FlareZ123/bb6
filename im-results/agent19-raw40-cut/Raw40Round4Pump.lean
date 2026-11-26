import Agent46AutoPump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Round4
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto

namespace Leaf14
-- 1RB0LA1RC1LB0RD0RE1LD1LA---0LF0RF0RC
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def cert : Cert := ⟨3, ⟨3, .periodic [] [false,false,false] (.lit [false,false,true,true]), .lit []⟩, 1,
  [.left [] [] [false,false,false] [true,true,true] (.lit [false,false,true,true]) (.lit []) 3] ++ List.replicate 6 Action.step ++ [.right [true] [true,true] [true,true,true] [false,false,false] (.lit [true,true]) (.lit []) 5] ++ List.replicate 6 Action.step, 8, 12⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf14


namespace Leaf40
-- 1RB0LA1RC1LB0RD0RE1LD1LA0RF0RC1LA---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def cert : Cert := ⟨69, ⟨4, .lit [true,false,false,false,false,false,false,false,false,false,false,false,true], .periodic [] [true,true,true,true] (.lit [])⟩, 1,
  [.right [true,false,false,false,false,false,false,false,false,false,false,false] [] [true,true,true,true] [false,false,false,false] (.lit [true]) (.lit []) 4] ++ List.replicate 2 Action.step ++ [.left [false,false,false,false,false,false,false,false,false,false,false,false,false,false] [] [false,false,false,false] [true,true,true,true] (.lit [true]) (.lit []) 4] ++ List.replicate 30 Action.step, 8, 32⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf40


namespace Leaf41
-- 1RB0LA1RC1LB0RD0RE1LD1LA0RF0RC1LC---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | _,_ => none

def cert : Cert := ⟨71, ⟨4, .lit [true,false,false,false,false,false,false,false,false,false,false,false,true], .periodic [] [true,true,true,true] (.lit [])⟩, 1,
  [.right [true,false,false,false,false,false,false,false,false,false,false,false] [] [true,true,true,true] [false,false,false,false] (.lit [true]) (.lit []) 4] ++ List.replicate 2 Action.step ++ [.left [false,false,false,false,false,false,false,false,false,false,false,false,false,false] [] [false,false,false,false] [true,true,true,true] (.lit [true]) (.lit []) 4] ++ List.replicate 30 Action.step, 8, 32⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf41


namespace Leaf43
-- 1RB0LA1RC1LB0RD0RE1LD1LA0RF0RC1RA---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | _,_ => none

def cert : Cert := ⟨103, ⟨4, .lit [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true], .periodic [] [true,true,true,true] (.lit [])⟩, 1,
  [.right [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] [] [true,true,true,true] [false,false,false,false] (.lit [true]) (.lit []) 4] ++ List.replicate 2 Action.step ++ [.left [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] [] [false,false,false,false] [true,true,true,true] (.lit [true]) (.lit []) 4] ++ List.replicate 38 Action.step, 8, 40⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf43


namespace Leaf44
-- 1RB0LA1RC1LB0RD0RE1LD1LA0RF0RC1RC---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | _,_ => none

def cert : Cert := ⟨83, ⟨4, .lit [true,false,false,false,false,false,false,false,false,false,false,false,false,false,true], .periodic [] [true,true,true,true] (.lit [])⟩, 1,
  [.right [true,false,false,false,false,false,false,false,false,false,false,false,false,false] [] [true,true,true,true] [false,false,false,false] (.lit [true]) (.lit []) 4] ++ List.replicate 2 Action.step ++ [.left [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] [] [false,false,false,false] [true,true,true,true] (.lit [true]) (.lit []) 4] ++ List.replicate 34 Action.step, 8, 36⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf44


namespace Leaf60
-- 1RB0LA1RC1LB0RD0RE1LD1LA1RF0RC1LB---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def cert : Cert := ⟨67, ⟨4, .lit [true,false,false,false,false,false,false,false,false,false,false,false,true], .periodic [] [true,true,true,true] (.lit [])⟩, 1,
  [.right [true,false,false,false,false,false,false,false,false,false,false,false] [] [true,true,true,true] [false,false,false,false] (.lit [true]) (.lit []) 4] ++ List.replicate 2 Action.step ++ [.left [false,false,false,false,false,false,false,false,false,false,false,false,false,false] [] [false,false,false,false] [true,true,true,true] (.lit [true]) (.lit []) 4] ++ List.replicate 30 Action.step, 8, 32⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf60


namespace Leaf62
-- 1RB0LA1RC1LB0RD0RE1LD1LA1RF0RC1RB---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none

def cert : Cert := ⟨64, ⟨4, .lit [true,false,false,false,false,false,false,false,false,false,false,false,true], .periodic [] [true,true,true,true] (.lit [])⟩, 1,
  [.right [true,false,false,false,false,false,false,false,false,false,false,false] [] [true,true,true,true] [false,false,false,false] (.lit [true]) (.lit []) 4] ++ List.replicate 2 Action.step ++ [.left [false,false,false,false,false,false,false,false,false,false,false,false,false,false] [] [false,false,false,false] [true,true,true,true] (.lit [true]) (.lit []) 4] ++ List.replicate 30 Action.step, 8, 32⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf62


namespace Leaf87
-- 1RB0LA1RC1LB0RD0RE1LD1LA---0RF---0RC
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def cert : Cert := ⟨3, ⟨3, .periodic [] [false,false,false] (.lit [false,false,true,true]), .lit []⟩, 1,
  [.left [] [] [false,false,false] [true,true,true] (.lit [false,false,true,true]) (.lit []) 3] ++ List.replicate 6 Action.step ++ [.right [true] [true,true] [true,true,true] [false,false,false] (.lit [true,true]) (.lit []) 3] ++ List.replicate 4 Action.step, 6, 10⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf87


namespace Leaf174
-- 1RB0LA1RC1LB0RD0RE1LD1LA1RF1RD0LA---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none

def cert : Cert := ⟨62, ⟨1, .periodic [] [true,true] (.lit []), .lit [true,true,true,true,true,true,true,true,true,true]⟩, 1,
  [.left [] [true,true,true,true,true,true,true,true,true,true] [true,true] [true,true] (.lit []) (.lit []) 2] ++ List.replicate 1 Action.step ++ [.right [true,true] [true,true,true,true,true,true,true,true,true] [true,true] [true,true] (.lit []) (.lit []) 6] ++ List.replicate 38 Action.step, 8, 39⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf174


namespace Leaf198
-- 1RB0LA1RC1LB0RD0RE1LD1LA0RC1RF---0LC
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def cert : Cert := ⟨3, ⟨3, .periodic [] [false,false,false] (.lit [false,false,true,true]), .lit []⟩, 1,
  [.left [] [] [false,false,false] [true,true,true] (.lit [false,false,true,true]) (.lit []) 3] ++ List.replicate 6 Action.step ++ [.right [true] [true,true] [true,true,true] [false,false,false] (.lit [true,true]) (.lit []) 5] ++ List.replicate 6 Action.step, 8, 12⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf198


namespace Leaf267
-- 1RB0LA1RC1LB0RD1RE1LD1LA0RF0RB0LB---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def cert : Cert := ⟨54, ⟨1, .periodic [] [true,true,true,true] (.lit []), .lit [true,true,true,true,true,true,true,true,true,true]⟩, 1,
  [.left [] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true] (.lit []) (.lit []) 4] ++ List.replicate 1 Action.step ++ [.right [true,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true] (.lit []) (.lit []) 8] ++ List.replicate 32 Action.step, 12, 33⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf267


namespace Leaf288
-- 1RB0LA1RC1LB0RD1RE1LD1LA1RF0RB0RD---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | _,_ => none

def cert : Cert := ⟨50, ⟨1, .periodic [] [true,true,true,true] (.lit []), .lit [true,true,true,true,true,true,true,true,true,true]⟩, 1,
  [.left [] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true] (.lit []) (.lit []) 4] ++ List.replicate 1 Action.step ++ [.right [true,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true] (.lit []) (.lit []) 8] ++ List.replicate 32 Action.step, 12, 33⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf288


namespace Leaf291
-- 1RB0LA1RC1LB0RD1RE1LD1LA1RF0RB1RB---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none

def cert : Cert := ⟨58, ⟨1, .periodic [] [true,true,true,true] (.lit []), .lit [true,true,true,true,true,true,true,true,true,true,true,true]⟩, 1,
  [.left [] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true] (.lit []) (.lit []) 4] ++ List.replicate 1 Action.step ++ [.right [true,true] [true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true] (.lit []) (.lit []) 8] ++ List.replicate 38 Action.step, 12, 39⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf291


namespace Leaf310
-- 1RB0LA1RC1LB0RD1RE1LD1LA0LA0RF---0RB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def cert : Cert := ⟨14, ⟨3, .lit [false,false,true,false,false,true,true,true], .periodic [] [true,true,true] (.lit [])⟩, 1,
  List.replicate 5 Action.step ++ [.right [true,false] [true,true,true] [true,true,true] [false,true,true] (.lit [true,true,true]) (.lit []) 5] ++ List.replicate 9 Action.step ++ [.left [true,true,false,true,true] [false] [false,true,true] [true,true,true] (.lit [true,true,true]) (.lit []) 9] ++ List.replicate 28 Action.step, 14, 42⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf310


namespace Leaf312
-- 1RB0LA1RC1LB0RD1RE1LD1LA1RB0RF---0RB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def cert : Cert := ⟨14, ⟨3, .lit [false,false,true,false,false,true,true,true], .periodic [] [true,true,true,true,true,true] (.lit [])⟩, 1,
  List.replicate 5 Action.step ++ [.right [true,false] [true,true,true] [true,true,true,true,true,true] [false,true,true,false,true,true] (.lit [true,true,true]) (.lit []) 10] ++ List.replicate 11 Action.step ++ [.left [false,false,true,true,true,true,false,true,true] [] [false,true,true,false,true,true] [true,true,true,true,true,true] (.lit [true,true,true]) (.lit []) 18] ++ List.replicate 32 Action.step, 28, 48⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf312


namespace Leaf318
-- 1RB0LA1RC1LB0RD1RE1LD1LA---0RF1RA1RD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def cert : Cert := ⟨41, ⟨1, .periodic [] [true,true,true,true,true,true] (.lit []), .lit [true,true,true,true,true,true,true,true]⟩, 1,
  [.left [] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) 6] ++ List.replicate 1 Action.step ++ [.right [true,true] [true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) 14] ++ List.replicate 36 Action.step, 20, 37⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf318


namespace Leaf319
-- 1RB0LA1RC1LB0RD1RE1LD1LA---0RF1RB1RD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def cert : Cert := ⟨30, ⟨5, .periodic [true,false] [true,true,true,true,true,true] (.lit [true,true,true,true,true]), .lit []⟩, 1,
  List.replicate 4 Action.step ++ [.left [true,true] [true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit [true,true,true,true,true]) (.lit []) 6] ++ List.replicate 8 Action.step ++ [.right [true,true] [true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) 14] ++ List.replicate 27 Action.step, 20, 39⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf319


namespace Leaf320
-- 1RB0LA1RC1LB0RD1RE1LD1LA---0RF1RC1RD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def cert : Cert := ⟨20, ⟨1, .periodic [] [true,true,true,true,true,true] (.lit []), .lit [true,true,true,true,true,true]⟩, 1,
  [.left [] [true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) 6] ++ List.replicate 1 Action.step ++ [.right [true,true] [true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) 14] ++ List.replicate 13 Action.step ++ [.left [true,true,true,true,true,true,true] [true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) 6] ++ List.replicate 8 Action.step ++ [.right [true,true] [true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) 14] ++ List.replicate 26 Action.step, 40, 48⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf320


namespace Leaf321
-- 1RB0LA1RC1LB0RD1RE1LD1LA---0RF1RD1RD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def cert : Cert := ⟨31, ⟨3, .periodic [false,true,false] [true,true,true] (.lit [true,true,true,true,true]), .lit []⟩, 1,
  List.replicate 3 Action.step ++ [.left [true,true] [true] [true,true,true] [true,true,true] (.lit [true,true,true,true,true]) (.lit []) 3] ++ List.replicate 8 Action.step ++ [.right [true,true] [true,true,true,true,true,true,true] [true,true,true] [true,true,true] (.lit []) (.lit []) 7] ++ List.replicate 17 Action.step, 10, 28⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf321


namespace Leaf358
-- 1RB0LA1RC1LB0RD1RE1LD1LA---1RF0RA0RB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def cert : Cert := ⟨12, ⟨1, .periodic [false,false] [true,true,true,true,true,true,true,true,true] (.lit [true,true,true,true]), .lit []⟩, 1,
  List.replicate 6 Action.step ++ [.left [true,true] [true,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] (.lit [true,true,true,true]) (.lit []) 9] ++ List.replicate 7 Action.step ++ [.right [true,true] [true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] (.lit []) (.lit []) 15] ++ List.replicate 25 Action.step, 24, 38⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf358


namespace Leaf359
-- 1RB0LA1RC1LB0RD1RE1LD1LA0LA1RF---0RC
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def cert : Cert := ⟨13, ⟨3, .lit [false,false,false,true,true,true,true], .periodic [] [true,true,true,true,true,true] (.lit [])⟩, 1,
  List.replicate 16 Action.step ++ [.right [true] [true,true,true,true,true,true] [true,true,true,true,true,true] [false,true,true,false,true,true] (.lit [true,true]) (.lit []) 6] ++ List.replicate 12 Action.step ++ [.left [false,false,true,true,true,true,false,true,true] [] [false,true,true,false,true,true] [true,true,true,true,true,true] (.lit [true,true]) (.lit []) 18] ++ List.replicate 30 Action.step, 24, 58⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf359


namespace Leaf360
-- 1RB0LA1RC1LB0RD1RE1LD1LA0RA1RF---0RC
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def cert : Cert := ⟨48, ⟨5, .periodic [true,true,true,true] [true,true,false,true,true,false] (.lit [true,true,false,true,true,false,true,true,true,true]), .lit []⟩, 1,
  List.replicate 7 Action.step ++ [.left [true] [] [true,true,false,true,true,false] [true,true,true,true,true,true] (.lit [true,true,false,true,true,false,true,true,true,true]) (.lit [false,true,true,true,true]) 18] ++ List.replicate 52 Action.step ++ [.right [true] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true] [false,true,true,false,true,true] (.lit [true,true]) (.lit [false,true,true,true,true]) 6] ++ List.replicate 19 Action.step, 24, 78⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf360


namespace Leaf361
-- 1RB0LA1RC1LB0RD1RE1LD1LA1LA1RF---0RC
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def cert : Cert := ⟨41, ⟨4, .periodic [false,true,true,true] [true,true,false] (.lit [true,true,false,true,true,true,true]), .periodic [] [true] (.lit [])⟩, 1,
  List.replicate 3 Action.step ++ [.left [true] [] [true,true,false] [true,true,true] (.lit [true,true,false,true,true,true,true]) (.periodic [false,false,true] [true] (.lit [])) 9] ++ List.replicate 43 Action.step ++ [.right [true] [true,true,true,true,true,true,true,true,true] [true,true,true] [false,true,true] (.lit [true,true]) (.periodic [false,false,true] [true] (.lit [])) 3] ++ List.replicate 15 Action.step, 12, 61⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf361


namespace Leaf362
-- 1RB0LA1RC1LB0RD1RE1LD1LA1RA1RF---0RC
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def cert : Cert := ⟨13, ⟨3, .lit [false,false,false,true,true,true,true], .periodic [] [true,true,true,true,true,true,true,true,true] (.lit [])⟩, 1,
  List.replicate 16 Action.step ++ [.right [true] [true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true] [false,true,true,false,true,true,false,true,true] (.lit [true,true]) (.lit []) 9] ++ List.replicate 11 Action.step ++ [.left [false,false,true,true,true,true,false,true,true,false,true,true] [] [false,true,true,false,true,true,false,true,true] [true,true,true,true,true,true,true,true,true] (.lit [true,true]) (.lit []) 27] ++ List.replicate 39 Action.step, 36, 66⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf362

end BB6.Agent19Raw40.Round4
