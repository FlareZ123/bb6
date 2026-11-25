import Agent46Auto2Counter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto2.Counter.Raw13Double1LE
open BB6Coverage Agent31Pump Auto2 Counter

-- 1RB1LC1RC0LD1LA0RB1LE1LB0LF1LF1RB---
def p4 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => none
  | _,_ => none

def c4 : Cert := ⟨⟨4,(.lit []),(.periodic [true,false] [true,false,true,false,true,false,true,false] false (.periodic [true] [true,true,true,true] true (.lit [])))⟩,7,0,1,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.periodic [true,true,true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,true,true] [true,true,true,true] true (.lit [])) false 12,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .right [true] [false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true] [true,true,true,true] true (.lit [])) false 12,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],40,36,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.lit [true]) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,true,true,true,true,true,true,true] (.lit [true]) (.lit []) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],16,16⟩
theorem checked4 : c4.check p4 = true := by decide
theorem never4 (m : Machine) (hm : compatible p4 m) : NeverHalts m := c4.never p4 checked4 m hm
#print axioms never4

-- 1RB1LC1RC0LD1LA0RB1LE---1RF1RC1RA0RF
def p7 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => none
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def c7 : Cert := ⟨⟨1,(.periodic [false,false,true,false,true,false] [true,false,true,false] false (.periodic [true,true] [true,true] true (.lit []))),(.lit [])⟩,28,0,3,[
    .step,
    .left [false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.periodic [true,true,true,true] [true,true] true (.lit [])) (.lit []) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .right [true,true] [true,true,true,true,true,true,true,true] [true,true,true,true] [false,true,false,true] (.periodic [true] [true,true] true (.lit [])) (.lit []) false 12,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],16,34,[
    .step,
    .left [false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true,true]) (.lit []) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .right [true] [false,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true] (.lit [true]) (.lit []) false 28,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],32,75⟩
theorem checked7 : c7.check p7 = true := by decide
theorem never7 (m : Machine) (hm : compatible p7 m) : NeverHalts m := c7.never p7 checked7 m hm
#print axioms never7

-- 1RB1LC1RC0LD1LA0RB1LE---1RE0RF1RA1LB
def p8 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => none
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def c8 : Cert := ⟨⟨1,(.periodic [false,false,true,false,true,false] [true,false,true,false] false (.periodic [true,true] [true,true] true (.lit []))),(.lit [])⟩,30,0,3,[
    .step,
    .left [false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.periodic [true,true,true,true] [true,true] true (.lit [])) (.lit []) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .right [true,true] [true,true,true,true,true,true,true,true] [true,true,true,true] [false,true,false,true] (.periodic [true] [true,true] true (.lit [])) (.lit []) false 16,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],20,42,[
    .step,
    .left [false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true,true]) (.lit []) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .right [true] [false,true,true,true,true,true,true,true] [true,true,true,true] [true,true,true,true] (.lit [true]) (.lit []) false 28,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],32,77⟩
theorem checked8 : c8.check p8 = true := by decide
theorem never8 (m : Machine) (hm : compatible p8 m) : NeverHalts m := c8.never p8 checked8 m hm
#print axioms never8

-- 1RB1LC1RC0LD1LA0RB1LE---0LA0LF1LE1LB
def p12 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => none
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def c12 : Cert := ⟨⟨4,(.lit []),(.periodic [true,false] [true,false,true,false,true,false,true,false] false (.periodic [true] [true,true,true,true] true (.lit [])))⟩,7,0,1,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.periodic [true,true,true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true] [] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,false,true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .right [true] [false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,false,true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,false,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],32,30,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.lit [true]) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,true,true,true,true,true,true,true] (.lit [true]) (.lit []) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],16,16⟩
theorem checked12 : c12.check p12 = true := by decide
theorem never12 (m : Machine) (hm : compatible p12 m) : NeverHalts m := c12.never p12 checked12 m hm
#print axioms never12

-- 1RB1LC1RC0LD1LA0RB1LE1LB0LA0LF0RC---
def p13 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => none
  | _,_ => none

def c13 : Cert := ⟨⟨4,(.lit []),(.periodic [true,false] [true,false,true,false,true,false,true,false] false (.periodic [true] [true,true,true,true] true (.lit [])))⟩,7,0,1,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.periodic [true,true,true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,true,true] [true,true,true,true] true (.lit [])) false 16,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .right [true] [false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true] [true,true,true,true] true (.lit [])) false 16,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],48,42,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.lit [true]) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,true,true,true,true,true,true,true] (.lit [true]) (.lit []) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],16,16⟩
theorem checked13 : c13.check p13 = true := by decide
theorem never13 (m : Machine) (hm : compatible p13 m) : NeverHalts m := c13.never p13 checked13 m hm
#print axioms never13

-- 1RB1LC1RC0LD1LA0RB1LE0RF0LA0LF1LB---
def p14 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => none
  | _,_ => none

def c14 : Cert := ⟨⟨4,(.lit [true]),(.periodic [true,false] [true,false,true,false] false (.periodic [true] [true,true] true (.lit [])))⟩,776,22,3,[
    .step,
    .step,
    .step,
    .right [true] [false,true,false] [true,false,true,false] [true,false,true,false] (.lit [true]) (.periodic [true,true,true] [true,true] true (.lit [])) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true,false] [] [true,false,true,false] [true,false,true,false] (.lit [true]) (.periodic [true] [true,true] true (.lit [])) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],8,14,[
    .step,
    .step,
    .step,
    .right [true] [false,true,false] [true,false,true,false] [true,false,true,false] (.lit [true]) (.lit [true]) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true]) (.lit []) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],8,26⟩
theorem checked14 : c14.check p14 = true := by decide
theorem never14 (m : Machine) (hm : compatible p14 m) : NeverHalts m := c14.never p14 checked14 m hm
#print axioms never14

-- 1RB1LC1RC0LD1LA0RB1LE0RB0LA0LF1LB---
def p15 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => none
  | _,_ => none

def c15 : Cert := ⟨⟨4,(.lit [true]),(.periodic [true,false,true,false,true,false] [true,false,true,false] false (.periodic [] [true,true] true (.lit [])))⟩,94,4,3,[
    .step,
    .step,
    .step,
    .right [true] [false,true,false,true,false,true,false] [true,false,true,false] [true,false,true,false] (.lit [true]) (.periodic [true,true] [true,true] true (.lit [])) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false] [true,false,true,false] (.lit [true]) (.periodic [] [true,true] true (.lit [])) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],8,22,[
    .step,
    .step,
    .step,
    .right [true] [false,true,false,true,false,true,false] [true,false,true,false] [true,false,true,false] (.lit [true]) (.lit []) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true]) (.lit []) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],8,43⟩
theorem checked15 : c15.check p15 = true := by decide
theorem never15 (m : Machine) (hm : compatible p15 m) : NeverHalts m := c15.never p15 checked15 m hm
#print axioms never15

-- 1RB1LC1RC0LD1LA0RB1LE1LB0LA0LF1LB---
def p16 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => none
  | _,_ => none

def c16 : Cert := ⟨⟨4,(.lit []),(.periodic [true,false] [true,false,true,false,true,false,true,false] false (.periodic [true] [true,true,true,true] true (.lit [])))⟩,7,0,1,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.periodic [true,true,true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .right [true] [false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],32,30,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.lit [true]) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,true,true,true,true,true,true,true] (.lit [true]) (.lit []) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],16,16⟩
theorem checked16 : c16.check p16 = true := by decide
theorem never16 (m : Machine) (hm : compatible p16 m) : NeverHalts m := c16.never p16 checked16 m hm
#print axioms never16

-- 1RB1LC1RC0LD1LA0RB1LE1LB0LA1LF1RB---
def p17 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,4⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => none
  | _,_ => none

def c17 : Cert := ⟨⟨4,(.lit []),(.periodic [true,false] [true,false,true,false,true,false,true,false] false (.periodic [true] [true,true,true,true] true (.lit [])))⟩,7,0,1,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.periodic [true,true,true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,true,true] [true,true,true,true] true (.lit [])) false 12,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .right [true] [false,true,false,true,false] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true,true,true] [true,true,true,true] true (.lit [])) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] (.lit [true]) (.periodic [true] [true,true,true,true] true (.lit [])) false 12,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],40,36,[
    .step,
    .step,
    .right [false] [true,false] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] (.lit [true]) (.lit [true]) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,true,true,true,true,true,true,true] (.lit [true]) (.lit []) false 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ],16,16⟩
theorem checked17 : c17.check p17 = true := by decide
theorem never17 (m : Machine) (hm : compatible p17 m) : NeverHalts m := c17.never p17 checked17 m hm
#print axioms never17
end BB6Coverage.Agent31Pump.Auto2.Counter.Raw13Double1LE
