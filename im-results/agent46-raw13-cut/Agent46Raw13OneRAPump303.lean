import Agent46AutoPump2
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13OneRA
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto2
def p303 : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,3,18,22,17,11,24]
def prepCert : Cert := ⟨⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true] false (.lit []))⟩,⟨1,(.periodic [false,false,true,false,true,false,true,false,false] [true,false] false (.lit [true,true,true,true])),(.lit [])⟩,(List.replicate 10 .step ++ [.right [true] [true,true,true] [true,true] [true,false] (.lit [true,true,true,true]) (.lit []) false 10] ++ List.replicate 66 .step),10,0,76⟩
theorem prepChecked : check p303 prepCert = true := by decide
def innerCert : Cert := ⟨⟨1,(.periodic [false,false,true,false,true,false,true,false] [true,false,true,false] false (.periodic [false,true,false] [true,false] true (.lit [true,true,true,true]))),(.lit [])⟩,⟨1,(.periodic [false,false,true,false,true,false,true,false,true,false,true,false] [true,false,true,false] false (.periodic [false] [true,false] true (.lit [true,true,true,true]))),(.lit [])⟩,(List.replicate 1 .step ++ [.left [false,true,false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.periodic [false,true,false] [true,false] true (.lit [true,true,true,true])) (.lit []) false 4] ++ List.replicate 9 .step ++ [.right [false,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,false,true,false] (.periodic [false] [true,false] true (.lit [true,true,true,true])) (.lit []) false 20] ++ List.replicate 48 .step),24,0,58⟩
theorem innerChecked : check p303 innerCert = true := by decide
def finishCert : Cert := ⟨⟨1,(.periodic [false,false,true,false,true,false,true,false] [true,false,true,false] false (.lit [false,true,true,true,true])),(.lit [])⟩,⟨0,(.lit []),(.periodic [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true] false (.lit []))⟩,(List.replicate 1 .step ++ [.left [false,true,false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit [false,true,true,true,true]) (.lit []) false 4] ++ List.replicate 9 .step ++ [.right [false,true] [true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,false,true,false] (.lit [true,true,true]) (.lit []) false 20] ++ List.replicate 49 .step ++ [.left [false,true,false,true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true,true,true]) (.lit []) false 4] ++ List.replicate 14 .step ++ [.right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true] [true,false,true,false] (.lit [true]) (.lit []) false 20] ++ List.replicate 72 .step ++ [.left [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true]) (.lit []) false 4] ++ List.replicate 19 .step),52,0,164⟩
theorem finishChecked : check p303 finishCert = true := by decide

def A (n : Nat) : Z0 := ⟨0,[],[true,true,true,true,true] ++ rep [true,true] n⟩
def B (k b : Nat) : Z0 := ⟨1,[false,false,true,false,true,false,true,false] ++ rep [true,false,true,false] k ++ [false] ++ rep [true,false] b ++ [true,true,true,true],[]⟩

theorem prepRun (n : Nat) : run0 p303 (10*n+76) (A n) = some (B 0 n) := by
  simpa [prepCert,PZ.eval,Word.eval,A,B,rep,List.append_assoc] using sound p303 prepCert prepChecked n 0

theorem innerRun (k b : Nat) : run0 p303 (24*k+58) (B k (b+1)) = some (B (k+1) b) := by
  simpa [innerCert,PZ.eval,Word.eval,B,rep,List.append_assoc] using sound p303 innerCert innerChecked k b

theorem rep_double (n : Nat) : rep [true,true] (2*n) = rep [true,true,true,true] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega]
    simp only [rep,ih]
    rfl

theorem finishRun (n : Nat) : run0 p303 (52*n+164) (B n 0) = some (A (2*n+7)) := by
  have h := sound p303 finishCert finishChecked n 0
  unfold A
  rw [show 2*n+7 = 7+2*n by omega, ← Auto.rep_add,rep_double]
  simpa [finishCert,PZ.eval,Word.eval,B,rep,List.append_assoc] using h

def drainCost : Nat → Nat → Nat
  | _,0 => 0
  | k,b+1 => (24*k+58)+drainCost (k+1) b

theorem drain (k b : Nat) : run0 p303 (drainCost k b) (B k b) = some (B (k+b) 0) := by
  induction b generalizing k with
  | zero => simp [drainCost,run0]
  | succ b ih =>
    rw [drainCost]
    have h := join0 (innerRun k b) (ih (k+1))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def cost (n : Nat) := (10*n+76)+drainCost 0 n+(52*n+164)
theorem growth (n : Nat) : run0 p303 (cost n) (A n) = some (A (2*n+7)) := by
  have h := drain 0 n
  simp only [Nat.zero_add] at h
  exact join0 (join0 (prepRun n) h) (finishRun n)

def index : Nat → Nat
  | 0 => 0
  | n+1 => 2*index n+7

theorem first : run0 p303 21 ⟨0,[],[]⟩ = some (A 0) := by decide

theorem never303 (m : Machine) (hm : compatible p303 m) : NeverHalts m := by
  apply never_of_growth p303 (fun k => A (index k)) 21 (fun k => cost (index k)) _ _ _ m hm
  · exact first
  · intro k; unfold cost; omega
  · intro k; simpa only [index] using growth (index k)
#print axioms growth
#print axioms never303
end BB6.Agent46Raw13OneRA
