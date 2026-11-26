import Agent46CounterCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Counter.Raw13Branch1046
open BB6Coverage Agent31Pump Auto Counter
def p0 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨false,true,4⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => none
  | _,_ => none
def c0 : Cert := ⟨⟨2,[false,false],[],[false,false,false],[true,false,false],[true],[false]⟩,63,[false,false],⟨[.step,.step,.step,.step,.step,.step],0,6⟩,
  ⟨[.step,.step,.step,.step,
    .right [false] [true,false,false] [true,false,false] [true,true,false] (.lit [false]) (.lit [false,false,false]) 3,
    .step,.step,.step,.step,.step,
    .left [false,true,true,false] [] [true,true,false] [false,false,false] (.lit [false]) (.lit [true,false,false]) 7,
    .step,.step,.step,.step,.step,.step,.step],10,16⟩,
  ⟨[.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],0,16⟩,
  ⟨[.step,.step,.step,.step,
    .right [false] [true,false,false] [true,false,false] [true,true,false] (.lit [false]) (.lit [true]) 3,
    .step,.step,.step,.step,.step,.step,.step,.step,
    .left [false,true,true,false,true,true,false] [] [true,true,false] [false,false,false] (.lit [false]) (.lit [true]) 7,
    .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],10,26⟩⟩
theorem checked0 : check p0 c0 = true := by decide
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m := never p0 c0 checked0 m hm
#print axioms never0
def p1 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨false,true,4⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none
def c1 : Cert := ⟨⟨0,[false],[true],[false,false,false],[false,true,false],[false,true],[false]⟩,36,[false],⟨[.step,.step,.step,.step,.step,.step,.step,.step],0,8⟩,
  ⟨[.step,.step,.step,
    .right [false] [false,true,false] [false,true,false] [true,true,false] (.lit [false]) (.lit [false,false,false]) 3,
    .step,.step,.step,.step,.step,.step,
    .left [true,false,true,true,false] [] [true,true,false] [false,false,false] (.lit [false]) (.lit [true,false]) 7,
    .step,.step,.step,.step,.step,.step,.step,.step,.step],10,18⟩,
  ⟨[.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],0,18⟩,
  ⟨[.step,.step,.step,
    .right [false] [false,true,false] [false,true,false] [true,true,false] (.lit [false]) (.lit [false,true]) 3,
    .step,.step,.step,.step,.step,.step,.step,.step,.step,
    .left [true,false,true,true,false,true,true,false] [] [true,true,false] [false,false,false] (.lit [false]) (.lit [true]) 7,
    .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],10,28⟩⟩
theorem checked1 : check p1 c1 = true := by decide
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m := never p1 c1 checked1 m hm
#print axioms never1
end BB6Coverage.Agent31Pump.Auto.Counter.Raw13Branch1046
