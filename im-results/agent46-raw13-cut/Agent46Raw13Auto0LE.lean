import Agent46AutoPump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Raw13Auto0LE
open BB6Coverage Agent31Pump Auto
def p0 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => none
  | _,_ => none

def c0 : Cert := ⟨568,⟨0,(.lit []),(.periodic [true,true,true,true,true,true,true,true,false,false,true,false] [false,true,false,false,true,true,true,true,true,true] (.lit [false,true,false,false,true,true,true,true,true,true,false,true,true,true,true,true,true]))⟩,1,(List.replicate 290 .step),0,290⟩
theorem checked0 : check p0 c0 = true := by decide
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m := check_never p0 c0 checked0 m hm
def p7 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => none
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def c7 : Cert := ⟨5,⟨1,(.periodic [true,false] [true,true,true] (.lit [])),(.lit [true])⟩,3,[.left [true,false] [] [true,true,true] [true,true,true] (.lit []) (.lit [true]) 27,.step,.step,.step,.right [false] [false] [true,true,true] [true,true,true] (.lit [true]) (.lit [true]) 7,.step,.step,.step,.step,.step,.step,.left [false,true,true,true,true] [] [true,true,true] [true,true,true] (.lit [true]) (.lit []) 27,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.right [false] [false,true,true,true,true] [true,true,true] [true,true,true] (.lit [true]) (.lit []) 7,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.left [false,true,true,true,true,true,true,true] [] [true,true,true] [true,true,true] (.lit [true]) (.lit []) 27,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.right [false] [false,true,true,true,true,true,true,true] [true,true,true] [true,true,true] (.lit [true]) (.lit []) 7,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],102,138⟩
theorem checked7 : check p7 c7 = true := by decide
theorem never7 (m : Machine) (hm : compatible p7 m) : NeverHalts m := check_never p7 c7 checked7 m hm
def p8 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => some (some ⟨false,false,5⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def c8 : Cert := ⟨8,⟨4,(.lit [false,true]),(.periodic [] [false,false] (.lit [false,true]))⟩,1,[.right [false] [] [false,false] [true,true] (.lit [true]) (.lit [false,true]) 2,.step,.step,.step,.left [true,true] [] [true,true] [false,false] (.lit [true]) (.lit [true]) 2,.step,.step,.step,.step,.step],4,8⟩
theorem checked8 : check p8 c8 = true := by decide
theorem never8 (m : Machine) (hm : compatible p8 m) : NeverHalts m := check_never p8 c8 checked8 m hm
def p9 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => some (some ⟨false,false,3⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,3⟩)
  | 5,true => none
  | _,_ => none

def c9 : Cert := ⟨8,⟨4,(.lit [false,true]),(.periodic [] [false,false,false] (.lit [false,true]))⟩,1,[.right [false] [] [false,false,false] [true,true,true] (.lit [true]) (.lit [false,true]) 3,.step,.step,.step,.step,.left [true,true,true] [] [true,true,true] [false,false,false] (.lit [true]) (.lit [true]) 3,.step,.step,.step,.step,.step,.step],6,10⟩
theorem checked9 : check p9 c9 = true := by decide
theorem never9 (m : Machine) (hm : compatible p9 m) : NeverHalts m := check_never p9 c9 checked9 m hm
def p12 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => some (some ⟨false,false,3⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => none
  | _,_ => none

def c12 : Cert := ⟨8,⟨4,(.lit [false,true]),(.periodic [] [false,false,false] (.lit [false,true]))⟩,1,[.right [false] [] [false,false,false] [true,true,true] (.lit [true]) (.lit [false,true]) 3,.step,.step,.step,.step,.step,.left [true,true] [] [true,true,true] [false,false,false] (.lit [true]) (.lit [false,true]) 3,.step,.step,.step,.step,.step],6,10⟩
theorem checked12 : check p12 c12 = true := by decide
theorem never12 (m : Machine) (hm : compatible p12 m) : NeverHalts m := check_never p12 c12 checked12 m hm
def p13 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => some (some ⟨false,false,5⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def c13 : Cert := ⟨8,⟨4,(.lit [false,true]),(.periodic [] [false,false] (.lit [false,true]))⟩,1,[.right [false] [] [false,false] [true,true] (.lit [true]) (.lit [false,true]) 2,.step,.step,.step,.step,.left [true] [] [true,true] [false,false] (.lit [true]) (.lit [false,true]) 2,.step,.step,.step,.step],4,8⟩
theorem checked13 : check p13 c13 = true := by decide
theorem never13 (m : Machine) (hm : compatible p13 m) : NeverHalts m := check_never p13 c13 checked13 m hm
def p14 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => some (some ⟨true,false,5⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => none
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def c14 : Cert := ⟨50,⟨4,(.periodic [false] [true,true,true] (.lit [true,true,true,true,true,true,true])),(.lit [false,true])⟩,1,[.step,.step,.left [true,true,true] [] [true,true,true] [true,true,false] (.lit [true,true,true,true,true,true,true]) (.lit []) 3,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.right [false] [false,true,true,false,true,true,false,true,true,false] [true,true,false] [true,true,true] (.lit [true]) (.lit []) 7,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],10,43⟩
theorem checked14 : check p14 c14 = true := by decide
theorem never14 (m : Machine) (hm : compatible p14 m) : NeverHalts m := check_never p14 c14 checked14 m hm
end BB6Coverage.Agent31Pump.Auto.Raw13Auto0LE
