import Agent46CounterCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Counter.Raw13Branch5421454
open BB6Coverage Agent31Pump Auto Counter
def p0 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,3⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none
def c0 : Cert := ⟨⟨0,[false],[true],[false,false,false],[false,false,true],[false,false,true],[false]⟩,19,[],⟨[.step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step],0,10⟩,
  ⟨[.step,
    .step,
    .step,
    .step,
    .right [false] [false,true] [false,false,true] [true,true,true] (.lit [false,false]) (.lit [false,false,false]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,true,true,true,true] [] [true,true,true] [false,false,false] (.lit [false,false]) (.lit [true]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step],6,16⟩,
  ⟨[.step,
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
    .step],0,16⟩,
  ⟨[.step,
    .step,
    .step,
    .step,
    .right [false] [false,true] [false,false,true] [true,true,true] (.lit [false,false]) (.lit [false,false,true]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,true,true,true,true,true,true,true] [] [true,true,true] [false,false,false] (.lit [false,false]) (.lit [true]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step],6,22⟩⟩
theorem checked0 : check p0 c0 = true := by decide
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m := never p0 c0 checked0 m hm
#print axioms never0
def p1 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,3⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => none
  | _,_ => none
def c1 : Cert := ⟨⟨0,[false],[true],[false,false,false],[false,true,false],[false,true],[false]⟩,17,[],⟨[.step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step],0,8⟩,
  ⟨[.step,
    .step,
    .step,
    .step,
    .right [false] [true,false] [false,true,false] [true,true,true] (.lit [false,false]) (.lit [false,false,false]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,true,true,true] [] [true,true,true] [false,false,false] (.lit [false,false]) (.lit [true,false]) 3,
    .step,
    .step,
    .step,
    .step,
    .step],6,14⟩,
  ⟨[.step,
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
    .step],0,14⟩,
  ⟨[.step,
    .step,
    .step,
    .step,
    .right [false] [true,false] [false,true,false] [true,true,true] (.lit [false,false]) (.lit [false,true]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,true,true,true,true,true,true] [] [true,true,true] [false,false,false] (.lit [false,false]) (.lit [true]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step],6,20⟩⟩
theorem checked1 : check p1 c1 = true := by decide
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m := never p1 c1 checked1 m hm
#print axioms never1
def p2 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,3⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none
def c2 : Cert := ⟨⟨0,[false],[true],[false,false,false],[false,false,true],[false,false,true],[false]⟩,20,[],⟨[.step,
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
    .step],0,12⟩,
  ⟨[.step,
    .step,
    .step,
    .step,
    .right [false] [false,true] [false,false,true] [true,false,true] (.lit [false,false]) (.lit [false,false,false]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,true,false,true] [] [true,false,true] [false,false,false] (.lit [false,false]) (.lit [true]) 5,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step],8,20⟩,
  ⟨[.step,
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
    .step],0,20⟩,
  ⟨[.step,
    .step,
    .step,
    .step,
    .right [false] [false,true] [false,false,true] [true,false,true] (.lit [false,false]) (.lit [false,false,true]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,true,false,true,true,false,true] [] [true,false,true] [false,false,false] (.lit [false,false]) (.lit [true]) 5,
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
    .step],8,28⟩⟩
theorem checked2 : check p2 c2 = true := by decide
theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m := never p2 c2 checked2 m hm
#print axioms never2
def p3 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,3⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => none
  | _,_ => none
def c3 : Cert := ⟨⟨0,[false],[true],[false,false,false],[false,true,false],[false,true],[false]⟩,32,[false],⟨[.step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step],0,8⟩,
  ⟨[.step,
    .step,
    .step,
    .step,
    .right [false] [true,false] [false,true,false] [true,false,true] (.lit [false,false]) (.lit [false,false,false]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,true,false,true] [] [true,false,true] [false,false,false] (.lit [false,false]) (.lit [true,false]) 5,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step],8,16⟩,
  ⟨[.step,
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
    .step],0,16⟩,
  ⟨[.step,
    .step,
    .step,
    .step,
    .right [false] [true,false] [false,true,false] [true,false,true] (.lit [false,false]) (.lit [false,true]) 3,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [true,true,false,true,true,false,true] [] [true,false,true] [false,false,false] (.lit [false,false]) (.lit [true]) 5,
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
    .step],8,24⟩⟩
theorem checked3 : check p3 c3 = true := by decide
theorem never3 (m : Machine) (hm : compatible p3 m) : NeverHalts m := never p3 c3 checked3 m hm
#print axioms never3
end BB6Coverage.Agent31Pump.Auto.Counter.Raw13Branch5421454
