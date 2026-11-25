import Agent46AutoPump
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13OneRE
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto
def p1007006 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,19,0,23,8,24,18]
def cert1007006 : Cert := ⟨4,⟨2,(.lit [true]),(.periodic [] [true,true,true,true] (.lit [true,true]))⟩,1,([.right [true] [] [true,true,true,true] [true,false,true,false] (.lit []) (.lit [true,true]) 16] ++ List.replicate 10 .step ++ [.left [false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit []) (.lit []) 4] ++ List.replicate 12 .step),20,22⟩
theorem ok1007006 : check p1007006 cert1007006 = true := by decide
theorem never1007006 (m : Machine) (hm : compatible p1007006 m) : NeverHalts m := check_never p1007006 cert1007006 ok1007006 m hm
#print axioms never1007006
def p1007026 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,19,13,1,23,24,7]
def cert1007026 : Cert := ⟨35,⟨2,(.periodic [] [false,true,true] (.lit [false,true,true,false])),(.lit [true,true,true,true,true])⟩,3,([.left [] [] [false,true,true] [true,true,true] (.lit [false,true,true,false]) (.lit [true,true,true,true,true]) 9] ++ List.replicate 11 .step ++ [.right [true,true] [true,true,true] [true,true,true] [true,true,false] (.lit []) (.lit [true,true,true,true,true]) 5] ++ List.replicate 29 .step ++ [.left [true,false,true,true,false,true,true,false,true,true,false] [] [true,true,false] [true,true,true] (.lit []) (.lit [true]) 9] ++ List.replicate 30 .step ++ [.right [true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,false] (.lit []) (.lit [true]) 5] ++ List.replicate 34 .step ++ [.left [true,false,true,true,false,true,true,false,true,true,false,true,true,false] [] [true,true,false] [true,true,true] (.lit []) (.lit [true]) 9] ++ List.replicate 39 .step ++ [.right [true,true] [true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,false] (.lit []) (.lit [true]) 5] ++ List.replicate 49 .step),42,192⟩
theorem ok1007026 : check p1007026 cert1007026 = true := by decide
theorem never1007026 (m : Machine) (hm : compatible p1007026 m) : NeverHalts m := check_never p1007026 cert1007026 ok1007026 m hm
#print axioms never1007026
def p1007029 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,19,15,1,23,24,7]
def cert1007029 : Cert := ⟨12,⟨0,(.lit []),(.periodic [true,true,true,true] [true,true,true,true,true,true] (.lit []))⟩,1,(List.replicate 1 .step ++ [.right [true,true] [true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) 10] ++ List.replicate 19 .step ++ [.left [true,false,true,true,true,true,true] [] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit [true,true]) 42] ++ List.replicate 32 .step),52,52⟩
theorem ok1007029 : check p1007029 cert1007029 = true := by decide
theorem never1007029 (m : Machine) (hm : compatible p1007029 m) : NeverHalts m := check_never p1007029 cert1007029 ok1007029 m hm
#print axioms never1007029
def p1007030 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,19,15,1,23,24,0]
def cert1007030 : Cert := ⟨1,⟨1,(.periodic [false] [true,false,true,true,false,true] (.lit [true])),(.lit [])⟩,1,(List.replicate 1 .step ++ [.left [false,true] [] [true,false,true,true,false,true] [true,true,true,true,true,true] (.lit [true]) (.lit []) 18] ++ List.replicate 11 .step ++ [.right [true,true] [true,true,true] [true,true,true,true,true,true] [false,true,true,false,true,true] (.lit []) (.lit []) 22] ++ List.replicate 16 .step),40,28⟩
theorem ok1007030 : check p1007030 cert1007030 = true := by decide
theorem never1007030 (m : Machine) (hm : compatible p1007030 m) : NeverHalts m := check_never p1007030 cert1007030 ok1007030 m hm
#print axioms never1007030
def p1007032 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,19,13,2,23,24,7]
def cert1007032 : Cert := ⟨22,⟨0,(.periodic [] [true,true,false] (.lit [true,true,false])),(.lit [true,true,true])⟩,1,([.left [] [] [true,true,false] [true,true,true] (.lit [true,true,false]) (.lit [true,true,true]) 7] ++ List.replicate 8 .step ++ [.right [true,true] [true,true] [true,true,true] [true,true,false] (.lit []) (.lit [true,true,true]) 5] ++ List.replicate 22 .step),12,30⟩
theorem ok1007032 : check p1007032 cert1007032 = true := by decide
theorem never1007032 (m : Machine) (hm : compatible p1007032 m) : NeverHalts m := check_never p1007032 cert1007032 ok1007032 m hm
#print axioms never1007032
def p1007034 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,19,15,2,23,24,7]
def cert1007034 : Cert := ⟨5,⟨1,(.periodic [true,false] [true,true,true] (.lit [])),(.lit [true])⟩,4,([.left [true,false] [] [true,true,true] [true,true,true] (.lit []) (.lit [true]) 15] ++ List.replicate 6 .step ++ [.right [true,true] [true,true] [true,true,true] [true,true,true] (.lit []) (.lit [true]) 5] ++ List.replicate 8 .step ++ [.left [false,true,true,true,true,true] [] [true,true,true] [true,true,true] (.lit []) (.lit []) 15] ++ List.replicate 24 .step ++ [.right [true,true] [true,true,true,true,true,true] [true,true,true] [true,true,true] (.lit []) (.lit []) 5] ++ List.replicate 13 .step ++ [.left [false,true,true,true,true,true,true,true,true] [] [true,true,true] [true,true,true] (.lit []) (.lit []) 15] ++ List.replicate 39 .step ++ [.right [true,true] [true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,true] (.lit []) (.lit []) 5] ++ List.replicate 18 .step ++ [.left [false,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true] [true,true,true] (.lit []) (.lit []) 15] ++ List.replicate 54 .step ++ [.right [true,true] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,true] (.lit []) (.lit []) 5] ++ List.replicate 26 .step),80,188⟩
theorem ok1007034 : check p1007034 cert1007034 = true := by decide
theorem never1007034 (m : Machine) (hm : compatible p1007034 m) : NeverHalts m := check_never p1007034 cert1007034 ok1007034 m hm
#print axioms never1007034
end BB6.Agent46Raw13OneRE
