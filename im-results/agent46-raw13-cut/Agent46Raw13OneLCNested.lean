import Agent46AutoPump2
import Agent46NestedPump
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13OneLC.M1003004
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto2 BB6Coverage.Agent31Pump.Nested
def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,10,17,15,21,24,19]
def prepCert : Cert := ⟨⟨0,(.lit []),(.periodic [true,true,true,true,true,true] [true,true] false (.lit [false]))⟩,⟨0,(.lit [false,true,false]),(.periodic [true,true,true,true] [true,true] false (.lit [false,false]))⟩,(List.replicate 5 .step ++ [.right [true] [true,true,true] [true,true] [true,false] (.lit [false,true,false]) (.lit [false]) false 2] ++ List.replicate 12 .step ++ [.left [false,true,false] [] [true,false] [true,true] (.lit [false,true,false]) (.lit [true,false,false]) false 2] ++ List.replicate 3 .step),4,0,20⟩
theorem prepChecked : check p prepCert = true := by decide
def innerCert : Cert := ⟨⟨0,(.periodic [false,true,false] [true,false] false (.lit [])),(.periodic [true,true,true,true] [true,true] true (.lit [false,false]))⟩,⟨0,(.periodic [false,true,false,true,false] [true,false] false (.lit [])),(.periodic [true,true] [true,true] true (.lit [false,false]))⟩,(List.replicate 5 .step ++ [.right [true] [true] [true,true] [true,false] (.periodic [false,true,false,true,false] [true,false] false (.lit [])) (.lit [false,false]) true 2] ++ List.replicate 10 .step ++ [.left [false] [] [true,false] [true,true] (.periodic [false,true,false,true,false] [true,false] false (.lit [])) (.lit [true,false,false]) true 2] ++ List.replicate 1 .step),0,4,16⟩
theorem innerChecked : check p innerCert = true := by decide
def finishCert : Cert := ⟨⟨0,(.periodic [false,true,false,true,false] [true,false] false (.lit [])),(.lit [true,true,false,false])⟩,⟨0,(.lit []),(.periodic [true,true,true,true,true,true,true,true] [true,true] false (.lit [false]))⟩,(List.replicate 10 .step ++ [.left [false,true,false,true,false,true,false] [] [true,false] [true,true] (.lit []) (.lit [true,false]) false 2] ++ List.replicate 7 .step),2,0,17⟩
theorem finishChecked : check p finishCert = true := by decide

def A (n : Nat) : Z0 := ⟨0,[],[true,true,true,true,true,true] ++ rep [true,true] n ++ [false]⟩
def B (k b _j : Nat) : Z0 := ⟨0,[false,true,false] ++ rep [true,false] k,[true,true] ++ rep [true,true] b ++ [false,false]⟩
theorem prepRun (n : Nat) : run0 p (4*n+20) (A n) = some (B 0 (n+1) 0) := by
  simpa [prepCert,PZ.eval,Word.eval,A,B,rep,List.append_assoc] using sound p prepCert prepChecked n 0

theorem innerRun (k b j : Nat) : run0 p (4*b+16) (B k (b+1) j) = some (B (k+1) b j) := by
  simpa [innerCert,PZ.eval,Word.eval,B,rep,List.append_assoc] using sound p innerCert innerChecked k b

theorem finishRun (n : Nat) : run0 p (2*n+17) (B (n+1) 0 0) = some (A (n+1)) := by
  simpa [finishCert,PZ.eval,Word.eval,A,B,rep,List.append_assoc] using sound p finishCert finishChecked n 0

def cost (n : Nat) := (4*n+20) + drainCost (fun _ b _ => 4*b+16) 0 0 (n+1) + (2*n+17)
theorem growth (n : Nat) : run0 p (cost n) (A n) = some (A (n+1)) := by
  have h := drain p B (fun _ b _ => 4*b+16) innerRun 0 (n+1) 0
  simp only [Nat.zero_add] at h
  exact join0 (join0 (prepRun n) h) (finishRun n)
theorem first : run0 p 25 ⟨0,[],[]⟩ = some (A 0) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p A 25 cost first _ growth m hm
  intro n; unfold cost; omega
#print axioms growth
#print axioms never
end BB6.Agent46Raw13OneLC.M1003004
