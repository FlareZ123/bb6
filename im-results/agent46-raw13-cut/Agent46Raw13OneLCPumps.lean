import Agent46AutoPump
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13OneLC
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto
def p1003006 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,10,17,15,21,24,3]
def cert1003006 : Cert := ⟨9,⟨1,(.lit [true,true]),(.periodic [] [true,true,true,true,true,true,true,true] (.lit [true,false,true]))⟩,1,(List.replicate 1 .step ++ [.right [true] [false] [true,true,true,true,true,true,true,true] [true,false,true,false,true,false,true,false] (.lit []) (.lit [true,false,true]) 28] ++ List.replicate 10 .step ++ [.left [false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,true,true,true,true,true,true,true] (.lit []) (.lit [true,false]) 8] ++ List.replicate 7 .step ++ [.right [true] [false,true,true,true,true] [true,true,true,true,true,true,true,true] [true,false,true,false,true,false,true,false] (.lit []) (.lit [true,false]) 28] ++ List.replicate 22 .step ++ [.left [false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,true,true,true,true,true,true,true] (.lit []) (.lit [true,false]) 8] ++ List.replicate 9 .step ++ [.right [true] [false,true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [true,false,true,false,true,false,true,false] (.lit []) (.lit [true,false]) 28] ++ List.replicate 40 .step ++ [.left [false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false] [true,true,true,true,true,true,true,true] (.lit []) (.lit [true,false,true]) 8] ++ List.replicate 10 .step),108,99⟩
theorem ok1003006 : check p1003006 cert1003006 = true := by decide
theorem never1003006 (m : Machine) (hm : compatible p1003006 m) : NeverHalts m := check_never p1003006 cert1003006 ok1003006 m hm
#print axioms never1003006
def p1003015 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,10,19,13,21,24,7]
def cert1003015 : Cert := ⟨5,⟨1,(.periodic [true,false] [false,true,false,true,false,true,false,true] (.lit [])),(.lit [true])⟩,1,(List.replicate 2 .step ++ [.left [] [] [false,true,false,true,false,true,false,true] [true,true,true,true,true,true,true,true] (.lit []) (.lit [true,false,true]) 8] ++ List.replicate 2 .step ++ [.right [true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit []) (.lit [true,false,true]) 12] ++ List.replicate 8 .step ++ [.left [false,true,false,true,false,true] [] [false,true,false,true,false,true,false,true] [true,true,true,true,true,true,true,true] (.lit []) (.lit [true]) 8] ++ List.replicate 8 .step ++ [.right [true,true] [true,true,true,true,true,true] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit []) (.lit [true]) 12] ++ List.replicate 16 .step),40,36⟩
theorem ok1003015 : check p1003015 cert1003015 = true := by decide
theorem never1003015 (m : Machine) (hm : compatible p1003015 m) : NeverHalts m := check_never p1003015 cert1003015 ok1003015 m hm
#print axioms never1003015
end BB6.Agent46Raw13OneLC
