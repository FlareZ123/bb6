import Agent46AutoPump
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13OneRA
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto
def p301 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,3,18,24,22,0,1]
def cert301 : Cert := ⟨12,⟨0,(.lit []),(.periodic [false] [true,true,false] (.lit [true,true,false]))⟩,1,(List.replicate 1 .step ++ [.right [false] [] [true,true,false] [true,true,true] (.lit [true]) (.lit [true,true,false]) 5] ++ List.replicate 6 .step ++ [.left [false,true,true,true,true] [] [true,true,true] [true,true,false] (.lit [true]) (.lit []) 11] ++ List.replicate 21 .step),16,28⟩
theorem ok301 : check p301 cert301 = true := by decide
theorem never301 (m : Machine) (hm : compatible p301 m) : NeverHalts m := check_never p301 cert301 ok301 m hm
#print axioms never301
def p304 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,3,18,20,6,15,24]
def cert304 : Cert := ⟨29,⟨5,(.lit []),(.periodic [false,true] [false,true,true] (.lit [false,true,true,false]))⟩,1,(List.replicate 3 .step ++ [.right [true] [true] [false,true,true] [true,true,true] (.lit [true]) (.lit [false,true,true,false]) 5] ++ List.replicate 16 .step ++ [.left [true,true,true,true,true,true,true] [] [true,true,true] [true,true,false] (.lit [true]) (.lit []) 3] ++ List.replicate 9 .step),8,28⟩
theorem ok304 : check p304 cert304 = true := by decide
theorem never304 (m : Machine) (hm : compatible p304 m) : NeverHalts m := check_never p304 cert304 ok304 m hm
#print axioms never304
def p305 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,3,18,22,6,17,24]
def cert305 : Cert := ⟨29,⟨5,(.lit []),(.periodic [true] [true,false,true] (.lit [true,false,true,true,false]))⟩,1,(List.replicate 2 .step ++ [.right [false] [true] [true,false,true] [true,true,true] (.lit []) (.lit [true,false,true,true,false]) 5] ++ List.replicate 17 .step ++ [.left [true,true,true,true,true,true,true,true] [] [true,true,true] [true,true,false] (.lit []) (.lit []) 3] ++ List.replicate 9 .step),8,28⟩
theorem ok305 : check p305 cert305 = true := by decide
theorem never305 (m : Machine) (hm : compatible p305 m) : NeverHalts m := check_never p305 cert305 ok305 m hm
#print axioms never305
def p306 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,3,18,22,6,11,24]
def cert306 : Cert := ⟨29,⟨5,(.lit []),(.periodic [true] [true,false,true] (.lit [true,false,true,true,false]))⟩,1,(List.replicate 1 .step ++ [.right [true] [] [true,false,true] [true,true,true] (.lit [true]) (.lit [true,false,true,true,false]) 5] ++ List.replicate 16 .step ++ [.left [true,true,true,true,true,true,true] [] [true,true,true] [true,true,false] (.lit [true]) (.lit []) 3] ++ List.replicate 9 .step),8,26⟩
theorem ok306 : check p306 cert306 = true := by decide
theorem never306 (m : Machine) (hm : compatible p306 m) : NeverHalts m := check_never p306 cert306 ok306 m hm
#print axioms never306
def p307 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,3,18,22,6,0,24]
def cert307 : Cert := ⟨29,⟨5,(.lit []),(.periodic [] [true,true,false,true,true,false] (.lit [true,true,false,true,true,false]))⟩,1,(List.replicate 2 .step ++ [.right [false] [] [true,true,false,true,true,false] [true,true,true,true,true,true] (.lit [true]) (.lit [true,true,false,true,true,false]) 10] ++ List.replicate 17 .step ++ [.left [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [true,true,false,true,true,false] (.lit [true]) (.lit []) 6] ++ List.replicate 10 .step ++ [.right [true] [true,false,true,true,false,true,true,false] [true,true,false,true,true,false] [true,true,true,true,true,true] (.lit [true]) (.lit []) 10] ++ List.replicate 21 .step ++ [.left [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [true,true,false,true,true,false] (.lit [true]) (.lit []) 6] ++ List.replicate 12 .step),32,62⟩
theorem ok307 : check p307 cert307 = true := by decide
theorem never307 (m : Machine) (hm : compatible p307 m) : NeverHalts m := check_never p307 cert307 ok307 m hm
#print axioms never307
end BB6.Agent46Raw13OneRA
