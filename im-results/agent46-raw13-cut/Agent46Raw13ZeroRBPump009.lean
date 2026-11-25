import Agent46NestedPump
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13ZeroRB.M999009
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.AutoN BB6Coverage.Agent31Pump.Nested
def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,5,19,21,23,24,15]
def innerCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] 0 (.periodic [true,true] [true,true] 1 (.periodic [false,true] [true] 2 (.lit [])))),(.lit [true])⟩,⟨0,(.periodic [true,false,true,false,true,false] [true,false,true,false] 0 (.periodic [] [true,true] 1 (.periodic [false,true] [true] 2 (.lit [])))),(.lit [true])⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.periodic [true,true] [true,true] 1 (.periodic [false,true] [true] 2 (.lit []))) (.lit [true]) 0 4] ++ List.replicate 3 .step ++ [.right [true] [true,true,true] [true,true,true,true] [true,false,true,false] (.periodic [] [true,true] 1 (.periodic [false,true] [true] 2 (.lit []))) (.lit [true]) 0 8] ++ List.replicate 11 .step),[(0,4),(0,8)],14⟩
theorem innerChecked : check p innerCert = true := by decide
def finishCert : Cert := ⟨⟨0,(.periodic [true,false,true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false,true,false,true,false] 0 (.periodic [false,true] [true] 2 (.lit []))),(.lit [true])⟩,⟨0,(.periodic [true,false,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] 0 (.periodic [false,true,true] [true] 2 (.lit []))),(.lit [true])⟩,([.left [true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false,true,false,true,false,true,false,true,false] [true,true,true,true,true,true,true,true,true,true,true,true] (.periodic [false,true] [true] 2 (.lit [])) (.lit [true]) 0 12] ++ List.replicate 14 .step ++ [.right [true] [true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true,true,true] (.periodic [false,true,true] [true] 2 (.lit [])) (.lit [true]) 0 12] ++ List.replicate 13 .step),[(0,12),(0,12)],27⟩
theorem finishChecked : check p finishCert = true := by decide

def B (k b j : Nat) : Z0 := ⟨0,[true,false] ++ rep [true,false,true,false] k ++ rep [true,true] b ++ [false,true] ++ rep [true] j,[true]⟩

def env (k b j : Nat) (i : Nat) := if i=0 then k else if i=1 then b else j

theorem innerRun (k b j : Nat) : run0 p (12*k+14) (B k (b+1) j) = some (B (k+1) b j) := by
  have h := sound p innerCert innerChecked (env k b j)
  simpa [innerCert,evalCosts,env,PZ.eval,Word.eval,B,rep,List.append_assoc,show 4*k+8*k+14=12*k+14 by omega] using h

theorem rep_alt12 (n : Nat) : rep [true,false,true,false,true,false,true,false,true,false,true,false] n = rep [true,false,true,false] (3*n) := rep_mul [true,false,true,false] 3 n
theorem rep_one12 (n : Nat) : rep [true,true,true,true,true,true,true,true,true,true,true,true] n = rep [true,true] (6*n) := rep_mul [true,true] 6 n

theorem finishRun (n j : Nat) : run0 p (24*n+27) (B (3*n+2) 0 j) = some (B 0 (6*n+5) (j+1)) := by
  have h := sound p finishCert finishChecked (env n 0 j)
  unfold B
  rw [show 3*n+2=2+3*n by omega, ← Auto.rep_add, ← rep_alt12,
      show 6*n+5=5+6*n by omega, ← Auto.rep_add, ← rep_one12]
  simpa [finishCert,evalCosts,env,PZ.eval,Word.eval,rep,List.append_assoc,show 12*n+12*n+27=24*n+27 by omega] using h

def A (n j : Nat) : Z0 := B 0 (3*n+2) j

def cost (n j : Nat) := drainCost (fun k _ _ => 12*k+14) 0 j (3*n+2) + (24*n+27)
theorem growth (n j : Nat) : run0 p (cost n j) (A n j) = some (A (2*n+1) (j+1)) := by
  have h := drain p B (fun k _ _ => 12*k+14) innerRun 0 (3*n+2) j
  simp only [Nat.zero_add] at h
  unfold A
  rw [show 3*(2*n+1)+2=6*n+5 by omega]
  exact join0 h (finishRun n j)

def index : Nat → Nat
  | 0 => 0
  | n+1 => 2*index n+1

theorem first : run0 p 26 ⟨0,[],[]⟩ = some (A 0 0) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => A (index k) k) 26 (fun k => cost (index k) k) _ _ _ m hm
  · exact first
  · intro k; unfold cost; omega
  · intro k; simpa only [index] using growth (index k) k
#print axioms growth
#print axioms never
end BB6.Agent46Raw13ZeroRB.M999009
namespace BB6.Agent46Raw13ZeroRB
open BB6Coverage
def p999009 := M999009.p
theorem never999009 (m : Machine) (hm : compatible p999009 m) : NeverHalts m := M999009.never m hm
end BB6.Agent46Raw13ZeroRB
