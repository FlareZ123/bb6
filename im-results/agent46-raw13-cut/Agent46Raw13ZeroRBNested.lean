import Agent46AutoPump2
import Agent46NestedPump
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13ZeroRB
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto2 BB6Coverage.Agent31Pump.Nested

def A (n : Nat) : Z0 := ⟨0,[],[true,true,true,true,true] ++ rep [true,true,true,true,true,true] n⟩
def B (k b _j : Nat) : Z0 := ⟨0,[true,false] ++ rep [true,false,true,false] k ++ [true] ++ rep [true,true] b,[true]⟩
def F (k : Nat) : Z0 := ⟨0,[],[true,true,true,true,true] ++ rep [true,true,true,true] k⟩

theorem rep6 (n : Nat) : rep [true,true,true,true,true,true] n = rep [true,true] (3*n) := rep_mul [true,true] 3 n
theorem rep4 (n : Nat) : rep [true,true,true,true] n = rep [true,true] (2*n) := rep_mul [true,true] 2 n

theorem F_eq_A (n : Nat) : F (3*n+3) = A (2*n+2) := by
  simp only [F,A,rep4,rep6,show 2*(3*n+3)=3*(2*n+2) by omega]

namespace M999013
def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,5,19,18,23,24,15]
def prepCert : Cert := ⟨⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true,true,true] false (.lit []))⟩,⟨0,(.periodic [true,false,true,true,true,true,true,true,true] [true,true,true,true,true,true] false (.lit [])),(.lit [true])⟩,(List.replicate 4 .step ++ [.right [true] [true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) false 6] ++ List.replicate 12 .step),6,0,16⟩
theorem prepChecked : check p prepCert = true := by decide
def innerCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.periodic [true,true,true] [true,true] true (.lit []))),(.lit [true])⟩,⟨0,(.periodic [true,false,true,false,true,false] [true,false,true,false] false (.periodic [true] [true,true] true (.lit []))),(.lit [true])⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.periodic [true,true,true] [true,true] true (.lit [])) (.lit [true]) false 4] ++ List.replicate 3 .step ++ [.right [true] [true,true,true] [true,true,true,true] [true,false,true,false] (.periodic [true] [true,true] true (.lit [])) (.lit [true]) false 8] ++ List.replicate 11 .step),12,0,14⟩
theorem innerChecked : check p innerCert = true := by decide
def finishCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.lit [true])),(.lit [true])⟩,⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true] false (.lit []))⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true]) (.lit [true]) false 4] ++ List.replicate 4 .step),4,0,4⟩
theorem finishChecked : check p finishCert = true := by decide

theorem prepRun (n : Nat) : run0 p (6*n+16) (A n) = some (B 0 (3*n+3) 0) := by
  have h := sound p prepCert prepChecked n 0
  unfold B
  rw [show 3*n+3=3+3*n by omega, ← Auto.rep_add, ← rep6]
  simpa [prepCert,PZ.eval,Word.eval,A,rep,List.append_assoc] using h

theorem innerRun (k b j : Nat) : run0 p (12*k+14) (B k (b+1) j) = some (B (k+1) b j) := by
  simpa [innerCert,PZ.eval,Word.eval,B,rep,List.append_assoc] using sound p innerCert innerChecked k b

theorem finishRun (k : Nat) : run0 p (4*k+4) (B k 0 0) = some (F k) := by
  simpa [finishCert,PZ.eval,Word.eval,B,F,rep,List.append_assoc] using sound p finishCert finishChecked k 0

def cost (n : Nat) := (6*n+16) + drainCost (fun k _ _ => 12*k+14) 0 0 (3*n+3) + (4*(3*n+3)+4)
theorem growth (n : Nat) : run0 p (cost n) (A n) = some (A (2*n+2)) := by
  have h := drain p B (fun k _ _ => 12*k+14) innerRun 0 (3*n+3) 0
  simp only [Nat.zero_add] at h
  rw [← F_eq_A]
  exact join0 (join0 (prepRun n) h) (finishRun (3*n+3))

def index : Nat → Nat
  | 0 => 0
  | n+1 => 2*index n+2

theorem first : run0 p 15 ⟨0,[],[]⟩ = some (A 0) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => A (index k)) 15 (fun k => cost (index k)) _ _ _ m hm
  · exact first
  · intro k; unfold cost; omega
  · intro k; simpa only [index] using growth (index k)
#print axioms never
end M999013
def p999013 := M999013.p
theorem never999013 (m : Machine) (hm : compatible p999013 m) : NeverHalts m := M999013.never m hm
namespace M999014
def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,5,19,15,21,24,1]
def prepCert : Cert := ⟨⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true,true,true] false (.lit []))⟩,⟨0,(.periodic [true,false,true,true,true,true,true,true,true] [true,true,true,true,true,true] false (.lit [])),(.lit [true])⟩,(List.replicate 1 .step ++ [.right [true,true] [true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) false 18] ++ List.replicate 17 .step),18,0,18⟩
theorem prepChecked : check p prepCert = true := by decide
def innerCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.periodic [true,true,true] [true,true] true (.lit []))),(.lit [true])⟩,⟨0,(.periodic [true,false,true,false,true,false] [true,false,true,false] false (.periodic [true] [true,true] true (.lit []))),(.lit [true])⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.periodic [true,true,true] [true,true] true (.lit [])) (.lit [true]) false 4] ++ List.replicate 3 .step ++ [.right [true] [true,true,true] [true,true,true,true] [true,false,true,false] (.periodic [true] [true,true] true (.lit [])) (.lit [true]) false 8] ++ List.replicate 11 .step),12,0,14⟩
theorem innerChecked : check p innerCert = true := by decide
def finishCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.lit [true])),(.lit [true])⟩,⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true] false (.lit []))⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true]) (.lit [true]) false 4] ++ List.replicate 4 .step),4,0,4⟩
theorem finishChecked : check p finishCert = true := by decide

theorem prepRun (n : Nat) : run0 p (18*n+18) (A n) = some (B 0 (3*n+3) 0) := by
  have h := sound p prepCert prepChecked n 0
  unfold B
  rw [show 3*n+3=3+3*n by omega, ← Auto.rep_add, ← rep6]
  simpa [prepCert,PZ.eval,Word.eval,A,rep,List.append_assoc] using h

theorem innerRun (k b j : Nat) : run0 p (12*k+14) (B k (b+1) j) = some (B (k+1) b j) := by
  simpa [innerCert,PZ.eval,Word.eval,B,rep,List.append_assoc] using sound p innerCert innerChecked k b

theorem finishRun (k : Nat) : run0 p (4*k+4) (B k 0 0) = some (F k) := by
  simpa [finishCert,PZ.eval,Word.eval,B,F,rep,List.append_assoc] using sound p finishCert finishChecked k 0

def cost (n : Nat) := (18*n+18) + drainCost (fun k _ _ => 12*k+14) 0 0 (3*n+3) + (4*(3*n+3)+4)
theorem growth (n : Nat) : run0 p (cost n) (A n) = some (A (2*n+2)) := by
  have h := drain p B (fun k _ _ => 12*k+14) innerRun 0 (3*n+3) 0
  simp only [Nat.zero_add] at h
  rw [← F_eq_A]
  exact join0 (join0 (prepRun n) h) (finishRun (3*n+3))

def index : Nat → Nat
  | 0 => 0
  | n+1 => 2*index n+2

theorem first : run0 p 15 ⟨0,[],[]⟩ = some (A 0) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => A (index k)) 15 (fun k => cost (index k)) _ _ _ m hm
  · exact first
  · intro k; unfold cost; omega
  · intro k; simpa only [index] using growth (index k)
#print axioms never
end M999014
def p999014 := M999014.p
theorem never999014 (m : Machine) (hm : compatible p999014 m) : NeverHalts m := M999014.never m hm
namespace M999015
def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,5,19,15,21,24,2]
def prepCert : Cert := ⟨⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true,true,true] false (.lit []))⟩,⟨0,(.periodic [true,false,true,true,true,true,true,true,true] [true,true,true,true,true,true] false (.lit [])),(.lit [true])⟩,(List.replicate 1 .step ++ [.right [true,true] [true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) false 14] ++ List.replicate 15 .step),14,0,16⟩
theorem prepChecked : check p prepCert = true := by decide
def innerCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.periodic [true,true,true] [true,true] true (.lit []))),(.lit [true])⟩,⟨0,(.periodic [true,false,true,false,true,false] [true,false,true,false] false (.periodic [true] [true,true] true (.lit []))),(.lit [true])⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.periodic [true,true,true] [true,true] true (.lit [])) (.lit [true]) false 4] ++ List.replicate 3 .step ++ [.right [true] [true,true,true] [true,true,true,true] [true,false,true,false] (.periodic [true] [true,true] true (.lit [])) (.lit [true]) false 8] ++ List.replicate 11 .step),12,0,14⟩
theorem innerChecked : check p innerCert = true := by decide
def finishCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.lit [true])),(.lit [true])⟩,⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true] false (.lit []))⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true]) (.lit [true]) false 4] ++ List.replicate 4 .step),4,0,4⟩
theorem finishChecked : check p finishCert = true := by decide

theorem prepRun (n : Nat) : run0 p (14*n+16) (A n) = some (B 0 (3*n+3) 0) := by
  have h := sound p prepCert prepChecked n 0
  unfold B
  rw [show 3*n+3=3+3*n by omega, ← Auto.rep_add, ← rep6]
  simpa [prepCert,PZ.eval,Word.eval,A,rep,List.append_assoc] using h

theorem innerRun (k b j : Nat) : run0 p (12*k+14) (B k (b+1) j) = some (B (k+1) b j) := by
  simpa [innerCert,PZ.eval,Word.eval,B,rep,List.append_assoc] using sound p innerCert innerChecked k b

theorem finishRun (k : Nat) : run0 p (4*k+4) (B k 0 0) = some (F k) := by
  simpa [finishCert,PZ.eval,Word.eval,B,F,rep,List.append_assoc] using sound p finishCert finishChecked k 0

def cost (n : Nat) := (14*n+16) + drainCost (fun k _ _ => 12*k+14) 0 0 (3*n+3) + (4*(3*n+3)+4)
theorem growth (n : Nat) : run0 p (cost n) (A n) = some (A (2*n+2)) := by
  have h := drain p B (fun k _ _ => 12*k+14) innerRun 0 (3*n+3) 0
  simp only [Nat.zero_add] at h
  rw [← F_eq_A]
  exact join0 (join0 (prepRun n) h) (finishRun (3*n+3))

def index : Nat → Nat
  | 0 => 0
  | n+1 => 2*index n+2

theorem first : run0 p 15 ⟨0,[],[]⟩ = some (A 0) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => A (index k)) 15 (fun k => cost (index k)) _ _ _ m hm
  · exact first
  · intro k; unfold cost; omega
  · intro k; simpa only [index] using growth (index k)
#print axioms never
end M999015
def p999015 := M999015.p
theorem never999015 (m : Machine) (hm : compatible p999015 m) : NeverHalts m := M999015.never m hm
namespace M999016
def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,5,19,15,23,24,12]
def prepCert : Cert := ⟨⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true,true,true] false (.lit []))⟩,⟨0,(.periodic [true,false,true,true,true,true,true,true,true] [true,true,true,true,true,true] false (.lit [])),(.lit [true])⟩,(List.replicate 2 .step ++ [.right [true] [false,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit []) (.lit []) false 10] ++ List.replicate 12 .step),10,0,14⟩
theorem prepChecked : check p prepCert = true := by decide
def innerCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.periodic [true,true,true] [true,true] true (.lit []))),(.lit [true])⟩,⟨0,(.periodic [true,false,true,false,true,false] [true,false,true,false] false (.periodic [true] [true,true] true (.lit []))),(.lit [true])⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.periodic [true,true,true] [true,true] true (.lit [])) (.lit [true]) false 4] ++ List.replicate 3 .step ++ [.right [true] [true,true,true] [true,true,true,true] [true,false,true,false] (.periodic [true] [true,true] true (.lit [])) (.lit [true]) false 8] ++ List.replicate 11 .step),12,0,14⟩
theorem innerChecked : check p innerCert = true := by decide
def finishCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.lit [true])),(.lit [true])⟩,⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true] false (.lit []))⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true]) (.lit [true]) false 4] ++ List.replicate 4 .step),4,0,4⟩
theorem finishChecked : check p finishCert = true := by decide

theorem prepRun (n : Nat) : run0 p (10*n+14) (A n) = some (B 0 (3*n+3) 0) := by
  have h := sound p prepCert prepChecked n 0
  unfold B
  rw [show 3*n+3=3+3*n by omega, ← Auto.rep_add, ← rep6]
  simpa [prepCert,PZ.eval,Word.eval,A,rep,List.append_assoc] using h

theorem innerRun (k b j : Nat) : run0 p (12*k+14) (B k (b+1) j) = some (B (k+1) b j) := by
  simpa [innerCert,PZ.eval,Word.eval,B,rep,List.append_assoc] using sound p innerCert innerChecked k b

theorem finishRun (k : Nat) : run0 p (4*k+4) (B k 0 0) = some (F k) := by
  simpa [finishCert,PZ.eval,Word.eval,B,F,rep,List.append_assoc] using sound p finishCert finishChecked k 0

def cost (n : Nat) := (10*n+14) + drainCost (fun k _ _ => 12*k+14) 0 0 (3*n+3) + (4*(3*n+3)+4)
theorem growth (n : Nat) : run0 p (cost n) (A n) = some (A (2*n+2)) := by
  have h := drain p B (fun k _ _ => 12*k+14) innerRun 0 (3*n+3) 0
  simp only [Nat.zero_add] at h
  rw [← F_eq_A]
  exact join0 (join0 (prepRun n) h) (finishRun (3*n+3))

def index : Nat → Nat
  | 0 => 0
  | n+1 => 2*index n+2

theorem first : run0 p 15 ⟨0,[],[]⟩ = some (A 0) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => A (index k)) 15 (fun k => cost (index k)) _ _ _ m hm
  · exact first
  · intro k; unfold cost; omega
  · intro k; simpa only [index] using growth (index k)
#print axioms never
end M999016
def p999016 := M999016.p
theorem never999016 (m : Machine) (hm : compatible p999016 m) : NeverHalts m := M999016.never m hm
namespace M999017
def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,5,19,15,23,24,15]
def prepCert : Cert := ⟨⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true,true,true] false (.lit []))⟩,⟨0,(.periodic [true,false,true,true,true,true,true,true,true] [true,true,true,true,true,true] false (.lit [])),(.lit [true])⟩,(List.replicate 4 .step ++ [.right [true] [true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit [true,true]) (.lit []) false 6] ++ List.replicate 8 .step),6,0,12⟩
theorem prepChecked : check p prepCert = true := by decide
def innerCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.periodic [true,true,true] [true,true] true (.lit []))),(.lit [true])⟩,⟨0,(.periodic [true,false,true,false,true,false] [true,false,true,false] false (.periodic [true] [true,true] true (.lit []))),(.lit [true])⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.periodic [true,true,true] [true,true] true (.lit [])) (.lit [true]) false 4] ++ List.replicate 3 .step ++ [.right [true] [true,true,true] [true,true,true,true] [true,false,true,false] (.periodic [true] [true,true] true (.lit [])) (.lit [true]) false 8] ++ List.replicate 11 .step),12,0,14⟩
theorem innerChecked : check p innerCert = true := by decide
def finishCert : Cert := ⟨⟨0,(.periodic [true,false] [true,false,true,false] false (.lit [true])),(.lit [true])⟩,⟨0,(.lit []),(.periodic [true,true,true,true,true] [true,true,true,true] false (.lit []))⟩,([.left [true,false] [] [true,false,true,false] [true,true,true,true] (.lit [true]) (.lit [true]) false 4] ++ List.replicate 4 .step),4,0,4⟩
theorem finishChecked : check p finishCert = true := by decide

theorem prepRun (n : Nat) : run0 p (6*n+12) (A n) = some (B 0 (3*n+3) 0) := by
  have h := sound p prepCert prepChecked n 0
  unfold B
  rw [show 3*n+3=3+3*n by omega, ← Auto.rep_add, ← rep6]
  simpa [prepCert,PZ.eval,Word.eval,A,rep,List.append_assoc] using h

theorem innerRun (k b j : Nat) : run0 p (12*k+14) (B k (b+1) j) = some (B (k+1) b j) := by
  simpa [innerCert,PZ.eval,Word.eval,B,rep,List.append_assoc] using sound p innerCert innerChecked k b

theorem finishRun (k : Nat) : run0 p (4*k+4) (B k 0 0) = some (F k) := by
  simpa [finishCert,PZ.eval,Word.eval,B,F,rep,List.append_assoc] using sound p finishCert finishChecked k 0

def cost (n : Nat) := (6*n+12) + drainCost (fun k _ _ => 12*k+14) 0 0 (3*n+3) + (4*(3*n+3)+4)
theorem growth (n : Nat) : run0 p (cost n) (A n) = some (A (2*n+2)) := by
  have h := drain p B (fun k _ _ => 12*k+14) innerRun 0 (3*n+3) 0
  simp only [Nat.zero_add] at h
  rw [← F_eq_A]
  exact join0 (join0 (prepRun n) h) (finishRun (3*n+3))

def index : Nat → Nat
  | 0 => 0
  | n+1 => 2*index n+2

theorem first : run0 p 15 ⟨0,[],[]⟩ = some (A 0) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => A (index k)) 15 (fun k => cost (index k)) _ _ _ m hm
  · exact first
  · intro k; unfold cost; omega
  · intro k; simpa only [index] using growth (index k)
#print axioms never
end M999017
def p999017 := M999017.p
theorem never999017 (m : Machine) (hm : compatible p999017 m) : NeverHalts m := M999017.never m hm
end BB6.Agent46Raw13ZeroRB
