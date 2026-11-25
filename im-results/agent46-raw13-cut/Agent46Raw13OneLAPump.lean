import Agent46AutoPump
import FastFAR
import Agent46CanonicalCut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13OneLA
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto
def pumpTable : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,2,17,15,23,24,7]
def pumpCert : Cert := ⟨14,⟨0,(.lit []),(.periodic [true] [true,true,true,true] (.lit [true,true,true]))⟩,1,(List.replicate 1 .step ++ [.right [true,true] [] [true,true,true,true] [true,false,true,false] (.lit []) (.lit [true,true,true]) 6] ++ List.replicate 12 .step ++ [.left [true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit []) (.lit [true,false,true]) 4] ++ List.replicate 5 .step ++ [.right [true,true] [true,true,true] [true,true,true,true] [true,false,true,false] (.lit []) (.lit [true,false,true]) 6] ++ List.replicate 10 .step ++ [.left [true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit []) (.lit [true,true]) 4] ++ List.replicate 6 .step),20,34⟩
theorem pumpChecked : BB6Coverage.Agent31Pump.Auto.check pumpTable pumpCert = true := by decide
 theorem pumpGrowth (n : Nat) : run0 pumpTable (20*n+34) (pumpCert.family.eval n) = some (pumpCert.family.eval (1+n)) := check_growth pumpTable pumpCert pumpChecked n
 theorem pumpNever (m : Machine) (hm : compatible pumpTable m) : NeverHalts m := check_never pumpTable pumpCert pumpChecked m hm
 #print axioms pumpGrowth
 #print axioms pumpNever

end BB6.Agent46Raw13OneLA
