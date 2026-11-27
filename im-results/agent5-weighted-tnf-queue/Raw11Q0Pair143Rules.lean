import Agent5TailPump
import Agent5MultiPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent31Pump.Tails.Raw11Q0Pair143
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay

namespace M0
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨false,true,4⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | 5,true => none
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 8,
  .steps 14,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],10,0,17⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_Q11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,true] true)⟩,⟨0,(.tail [false,false,true] false),(.tail [false] true)⟩,[.steps 5],0,0,5⟩
theorem check_Q11base : check table cert_Q11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_R5 : Cert := ⟨⟨0,(.tail [false,false] false),(.tail [false,true,true,true,true,true] true)⟩,⟨0,(.tail [false,false,true,false,true,true,false] false),(.tail [false] true)⟩,[.steps 21],0,0,21⟩
theorem check_R5 : check table cert_R5 = true := by decide +kernel

def cert_R1 : Cert := ⟨⟨0,(.tail [false,false] false),(.lit [false,true])⟩,⟨0,(.tail [true,true,true,false] false),(.lit [false,false,true])⟩,[.steps 12],0,0,12⟩
theorem check_R1 : check table cert_R1 = true := by decide +kernel

def cert_R2 : Cert := ⟨⟨0,(.tail [false,false] false),(.lit [false,true,true])⟩,⟨0,(.tail [true,true,true,false] false),(.lit [false,false,true])⟩,[.steps 8],0,0,8⟩
theorem check_R2 : check table cert_R2 = true := by decide +kernel

end M0

namespace M1
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 8,
  .steps 14,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],10,0,17⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_R1 : Cert := ⟨⟨0,(.tail [false,false] false),(.lit [false,true])⟩,⟨0,(.tail [true,true,true,false] false),(.lit [false,false,true])⟩,[.steps 12],0,0,12⟩
theorem check_R1 : check table cert_R1 = true := by decide +kernel

def cert_R2 : Cert := ⟨⟨0,(.tail [false,false] false),(.lit [false,true,true])⟩,⟨0,(.tail [true,true,true,false] false),(.lit [false,false,true])⟩,[.steps 8],0,0,8⟩
theorem check_R2 : check table cert_R2 = true := by decide +kernel

def cert_loop : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,true,true,true,true,true] true)⟩,⟨0,(.tail [true,true,false,true,true,false,true] false),(.tail [false] true)⟩,[.steps 23],0,0,23⟩
theorem check_loop : check table cert_loop = true := by decide +kernel

def cert_end2 : Cert := ⟨⟨0,(.tail [true,true] false),(.lit [false,true,true])⟩,⟨0,(.tail [true,true,true,false,true] false),(.lit [false,false,true])⟩,[.steps 17],0,0,17⟩
theorem check_end2 : check table cert_end2 = true := by decide +kernel

def cert_end3 : Cert := ⟨⟨0,(.tail [true,true] false),(.lit [false,true,true,true])⟩,⟨0,(.tail [true,true,true,false,true] false),(.lit [false,false,true])⟩,[.steps 13],0,0,13⟩
theorem check_end3 : check table cert_end3 = true := by decide +kernel

end M1

end BB6Coverage.Agent31Pump.Tails.Raw11Q0Pair143
