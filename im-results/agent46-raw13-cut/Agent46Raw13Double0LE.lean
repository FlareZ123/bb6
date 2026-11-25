import Agent46Auto2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto2.Raw13Double0LE
open BB6Coverage Agent31Pump Auto2
private def N (k m : Nat) : Bool → Nat := fun | false => k | true => m
private def Q : List Bool := [true,true]
private theorem append_shift (n k : Nat) : rep Q k ++ rep Q n = rep Q (k+n) := Auto.rep_add Q k n

def p1 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨false,true,4⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => none
  | _,_ => none
def prep1 : Macro := ⟨⟨0,(.lit []),(.periodic [true,true,true] [true,true] false (.lit []))⟩, ⟨4,(.periodic [true,true,true] [true,true] false (.lit [])),(.lit [false,false,true])⟩, [
    .step,
    .right [true,true] [true,true] [true,true] [true,true] (.lit []) (.lit []) false 6,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 6,0,16⟩
def loop1 : Macro := ⟨⟨4,(.periodic [true,true,true] [true,true] false (.lit [])),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.periodic [true] [true,true] false (.lit [])),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.periodic [true,true] [true,true] false (.lit [])) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.periodic [true,true] [true,true] false (.lit [])) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,16⟩
def finish1 : Macro := ⟨⟨4,(.lit [true]),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨0,(.lit []),(.periodic [true,true,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.lit []) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.lit []) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,14⟩
def G1 (n : Nat) : Z0 := ⟨0,[],[true,true,true] ++ rep Q (1*n)⟩
def F1 (k m : Nat) : Z0 := ⟨4,[true] ++ rep Q k,[false,false,true] ++ rep Q m⟩
theorem prepRun1 (n : Nat) : run0 p1 (6*n+16) (G1 n) = some (F1 (1*n+1) 0) := by
  have h := Macro.sound p1 prep1 (by decide) (N n 0)
  simpa [prep1,N,PZ.eval,Word.eval,G1,F1,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,rep_mul] using h

theorem loopRun1 (k m : Nat) : run0 p1 (10*m+16) (F1 (k+1) m) = some (F1 k (m+2)) := by
  have h := Macro.sound p1 loop1 (by decide) (N k m)
  simpa [loop1,N,PZ.eval,Word.eval,F1,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem finishRun1 (n : Nat) : run0 p1 (10*(0+2*(1*n+1))+14) (F1 0 (0+2*(1*n+1))) = some (G1 (2*n+4)) := by
  have h := Macro.sound p1 finish1 (by decide) (N 0 (0+2*(1*n+1)))
  unfold G1
  rw [show 1*(2*n+4) = (2)+(0+2*(1*n+1)) by omega, ← Auto.rep_add]
  simpa [finish1,N,PZ.eval,Word.eval,F1,G1,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

def cost1 (n : Nat) : Nat := (6*n+16)+drainCost 10 16 2 (1*n+1) 0+(10*(0+2*(1*n+1))+14)
theorem growth1 (n : Nat) : run0 p1 (cost1 n) (G1 n) = some (G1 (2*n+4)) := by
  exact join0 (join0 (prepRun1 n) (drain p1 F1 10 16 2 loopRun1 (1*n+1) 0)) (finishRun1 n)
theorem first1 : run0 p1 148 ⟨0,[],[]⟩ = some (G1 6) := by decide
theorem costPositive1 (n : Nat) : 0 < cost1 n := by unfold cost1; omega
#print axioms growth1
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m := never_of_map p1 G1 (fun n => 2*n+4) cost1 148 6 first1 costPositive1 growth1 m hm

def p2 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨false,true,4⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => none
  | _,_ => none
def prep2 : Macro := ⟨⟨0,(.lit []),(.periodic [true,true,true] [true,true] false (.lit []))⟩, ⟨4,(.periodic [true,true,true] [true,true] false (.lit [])),(.lit [false,false,true])⟩, [
    .step,
    .right [true,true] [true,true] [true,true] [true,true] (.lit []) (.lit []) false 6,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 6,0,16⟩
def loop2 : Macro := ⟨⟨4,(.periodic [true,true,true] [true,true] false (.lit [])),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.periodic [true] [true,true] false (.lit [])),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.periodic [true,true] [true,true] false (.lit [])) (.lit []) true 6,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.periodic [true,true] [true,true] false (.lit [])) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,8,14⟩
def finish2 : Macro := ⟨⟨4,(.lit [true]),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨0,(.lit []),(.periodic [true,true,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.lit []) (.lit []) true 6,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.lit []) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,8,12⟩
def G2 (n : Nat) : Z0 := ⟨0,[],[true,true,true] ++ rep Q (1*n)⟩
def F2 (k m : Nat) : Z0 := ⟨4,[true] ++ rep Q k,[false,false,true] ++ rep Q m⟩
theorem prepRun2 (n : Nat) : run0 p2 (6*n+16) (G2 n) = some (F2 (1*n+1) 0) := by
  have h := Macro.sound p2 prep2 (by decide) (N n 0)
  simpa [prep2,N,PZ.eval,Word.eval,G2,F2,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,rep_mul] using h

theorem loopRun2 (k m : Nat) : run0 p2 (8*m+14) (F2 (k+1) m) = some (F2 k (m+2)) := by
  have h := Macro.sound p2 loop2 (by decide) (N k m)
  simpa [loop2,N,PZ.eval,Word.eval,F2,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem finishRun2 (n : Nat) : run0 p2 (8*(0+2*(1*n+1))+12) (F2 0 (0+2*(1*n+1))) = some (G2 (2*n+4)) := by
  have h := Macro.sound p2 finish2 (by decide) (N 0 (0+2*(1*n+1)))
  unfold G2
  rw [show 1*(2*n+4) = (2)+(0+2*(1*n+1)) by omega, ← Auto.rep_add]
  simpa [finish2,N,PZ.eval,Word.eval,F2,G2,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

def cost2 (n : Nat) : Nat := (6*n+16)+drainCost 8 14 2 (1*n+1) 0+(8*(0+2*(1*n+1))+12)
theorem growth2 (n : Nat) : run0 p2 (cost2 n) (G2 n) = some (G2 (2*n+4)) := by
  exact join0 (join0 (prepRun2 n) (drain p2 F2 8 14 2 loopRun2 (1*n+1) 0)) (finishRun2 n)
theorem first2 : run0 p2 128 ⟨0,[],[]⟩ = some (G2 6) := by decide
theorem costPositive2 (n : Nat) : 0 < cost2 n := by unfold cost2; omega
#print axioms growth2
theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m := never_of_map p2 G2 (fun n => 2*n+4) cost2 128 6 first2 costPositive2 growth2 m hm

def p3 : PartialMachine := fun s => match s.1.val,s.2 with
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
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none
def prep3 : Macro := ⟨⟨4,(.lit []),(.periodic [false,false,true,true,true] [true,true] false (.lit []))⟩, ⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.lit [false,false,true,true,true])⟩, [
    .step,
    .right [false] [false,true,true,true] [true,true] [true,true] (.lit [true]) (.lit []) false 4,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 4,0,19⟩
def loop3 : Macro := ⟨⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.periodic [true,true] [true,true] false (.lit [])),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,16⟩
def finish3 : Macro := ⟨⟨4,(.lit [true,true]),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.lit []),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.lit [true]) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.lit [true]) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,16⟩
def G3 (n : Nat) : Z0 := ⟨4,[],[false,false,true,true,true] ++ rep Q (1*n)⟩
def F3 (k m : Nat) : Z0 := ⟨4,[true,true] ++ rep Q k,[false,false,true] ++ rep Q m⟩
theorem prepRun3 (n : Nat) : run0 p3 (4*n+19) (G3 n) = some (F3 (1*n+1) 1) := by
  have h := Macro.sound p3 prep3 (by decide) (N n 0)
  simpa [prep3,N,PZ.eval,Word.eval,G3,F3,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,rep_mul] using h

theorem loopRun3 (k m : Nat) : run0 p3 (10*m+16) (F3 (k+1) m) = some (F3 k (m+2)) := by
  have h := Macro.sound p3 loop3 (by decide) (N k m)
  simpa [loop3,N,PZ.eval,Word.eval,F3,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem finishRun3 (n : Nat) : run0 p3 (10*(1+2*(1*n+1))+16) (F3 0 (1+2*(1*n+1))) = some (G3 (2*n+4)) := by
  have h := Macro.sound p3 finish3 (by decide) (N 0 (1+2*(1*n+1)))
  unfold G3
  rw [show 1*(2*n+4) = (1)+(1+2*(1*n+1)) by omega, ← Auto.rep_add]
  simpa [finish3,N,PZ.eval,Word.eval,F3,G3,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

def cost3 (n : Nat) : Nat := (4*n+19)+drainCost 10 16 2 (1*n+1) 1+(10*(1+2*(1*n+1))+16)
theorem growth3 (n : Nat) : run0 p3 (cost3 n) (G3 n) = some (G3 (2*n+4)) := by
  exact join0 (join0 (prepRun3 n) (drain p3 F3 10 16 2 loopRun3 (1*n+1) 1)) (finishRun3 n)
theorem first3 : run0 p3 48 ⟨0,[],[]⟩ = some (G3 2) := by decide
theorem costPositive3 (n : Nat) : 0 < cost3 n := by unfold cost3; omega
#print axioms growth3
theorem never3 (m : Machine) (hm : compatible p3 m) : NeverHalts m := never_of_map p3 G3 (fun n => 2*n+4) cost3 48 2 first3 costPositive3 growth3 m hm

def p4 : PartialMachine := fun s => match s.1.val,s.2 with
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
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def prep4 : Macro := ⟨⟨4,(.lit []),(.periodic [false,false,true,true,true] [true,true] false (.lit []))⟩, ⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.lit [false,false,true,true,true])⟩, [
    .step,
    .step,
    .right [false] [true,true,true] [true,true] [true,true] (.lit [true,true]) (.lit []) false 6,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 6,0,21⟩
def loop4 : Macro := ⟨⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.periodic [true,true] [true,true] false (.lit [])),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,16⟩
def finish4 : Macro := ⟨⟨4,(.lit [true,true]),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.lit []),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.lit [true]) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.lit [true]) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,16⟩
def G4 (n : Nat) : Z0 := ⟨4,[],[false,false,true,true,true] ++ rep Q (1*n)⟩
def F4 (k m : Nat) : Z0 := ⟨4,[true,true] ++ rep Q k,[false,false,true] ++ rep Q m⟩
theorem prepRun4 (n : Nat) : run0 p4 (6*n+21) (G4 n) = some (F4 (1*n+1) 1) := by
  have h := Macro.sound p4 prep4 (by decide) (N n 0)
  simpa [prep4,N,PZ.eval,Word.eval,G4,F4,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,rep_mul] using h

theorem loopRun4 (k m : Nat) : run0 p4 (10*m+16) (F4 (k+1) m) = some (F4 k (m+2)) := by
  have h := Macro.sound p4 loop4 (by decide) (N k m)
  simpa [loop4,N,PZ.eval,Word.eval,F4,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem finishRun4 (n : Nat) : run0 p4 (10*(1+2*(1*n+1))+16) (F4 0 (1+2*(1*n+1))) = some (G4 (2*n+4)) := by
  have h := Macro.sound p4 finish4 (by decide) (N 0 (1+2*(1*n+1)))
  unfold G4
  rw [show 1*(2*n+4) = (1)+(1+2*(1*n+1)) by omega, ← Auto.rep_add]
  simpa [finish4,N,PZ.eval,Word.eval,F4,G4,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

def cost4 (n : Nat) : Nat := (6*n+21)+drainCost 10 16 2 (1*n+1) 1+(10*(1+2*(1*n+1))+16)
theorem growth4 (n : Nat) : run0 p4 (cost4 n) (G4 n) = some (G4 (2*n+4)) := by
  exact join0 (join0 (prepRun4 n) (drain p4 F4 10 16 2 loopRun4 (1*n+1) 1)) (finishRun4 n)
theorem first4 : run0 p4 48 ⟨0,[],[]⟩ = some (G4 2) := by decide
theorem costPositive4 (n : Nat) : 0 < cost4 n := by unfold cost4; omega
#print axioms growth4
theorem never4 (m : Machine) (hm : compatible p4 m) : NeverHalts m := never_of_map p4 G4 (fun n => 2*n+4) cost4 48 2 first4 costPositive4 growth4 m hm

def p5 : PartialMachine := fun s => match s.1.val,s.2 with
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
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
def prep5 : Macro := ⟨⟨4,(.lit []),(.periodic [false,false,true,true,true,true,true,true,true] [true,true,true,true,true,true] false (.lit []))⟩, ⟨4,(.periodic [true,true,true,true,true,true,true,true] [true,true,true,true,true,true] false (.lit [])),(.lit [false,false,true,true,true])⟩, [
    .step,
    .right [false] [false,true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit [true]) (.lit []) false 14,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 14,0,29⟩
def loop5 : Macro := ⟨⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.periodic [true,true] [true,true] false (.lit [])),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,16⟩
def finish5 : Macro := ⟨⟨4,(.lit [true,true]),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.lit []),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.lit [true]) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.lit [true]) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,16⟩
def G5 (n : Nat) : Z0 := ⟨4,[],[false,false,true,true,true,true,true,true,true] ++ rep Q (3*n)⟩
def F5 (k m : Nat) : Z0 := ⟨4,[true,true] ++ rep Q k,[false,false,true] ++ rep Q m⟩
theorem prepRun5 (n : Nat) : run0 p5 (14*n+29) (G5 n) = some (F5 (3*n+3) 1) := by
  have h := Macro.sound p5 prep5 (by decide) (N n 0)
  have hr : rep [true,true,true,true,true,true] n = rep Q (3*n) := by
    exact rep_mul Q 3 n
  simp only [prep5,N,PZ.eval,Word.eval] at h
  rw [hr] at h
  simpa [prep5,N,PZ.eval,Word.eval,G5,F5,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,rep_mul] using h

theorem loopRun5 (k m : Nat) : run0 p5 (10*m+16) (F5 (k+1) m) = some (F5 k (m+2)) := by
  have h := Macro.sound p5 loop5 (by decide) (N k m)
  simpa [loop5,N,PZ.eval,Word.eval,F5,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem finishRun5 (n : Nat) : run0 p5 (10*(1+2*(3*n+3))+16) (F5 0 (1+2*(3*n+3))) = some (G5 (2*n+2)) := by
  have h := Macro.sound p5 finish5 (by decide) (N 0 (1+2*(3*n+3)))
  have he : 1+2*(3*n+3) = 1+3*(2*n+2) := by omega
  simp only [finish5,N,PZ.eval,Word.eval,Nat.zero_mul,Nat.zero_add] at h
  rw [he] at h ⊢
  rw [show 1+3*(2*n+2) = 3*(2*n+2)+1 by omega] at h ⊢
  simpa [finish5,N,PZ.eval,Word.eval,F5,G5,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

def cost5 (n : Nat) : Nat := (14*n+29)+drainCost 10 16 2 (3*n+3) 1+(10*(1+2*(3*n+3))+16)
theorem growth5 (n : Nat) : run0 p5 (cost5 n) (G5 n) = some (G5 (2*n+2)) := by
  exact join0 (join0 (prepRun5 n) (drain p5 F5 10 16 2 loopRun5 (3*n+3) 1)) (finishRun5 n)
theorem first5 : run0 p5 48 ⟨0,[],[]⟩ = some (G5 0) := by decide
theorem costPositive5 (n : Nat) : 0 < cost5 n := by unfold cost5; omega
#print axioms growth5
theorem never5 (m : Machine) (hm : compatible p5 m) : NeverHalts m := never_of_map p5 G5 (fun n => 2*n+2) cost5 48 0 first5 costPositive5 growth5 m hm

def p6 : PartialMachine := fun s => match s.1.val,s.2 with
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
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none
def prep6 : Macro := ⟨⟨4,(.lit []),(.periodic [false,false,true,true,true,true,true,true,true] [true,true,true,true,true,true] false (.lit []))⟩, ⟨4,(.periodic [true,true,true,true,true,true,true,true] [true,true,true,true,true,true] false (.lit [])),(.lit [false,false,true,true,true])⟩, [
    .step,
    .right [false] [false,true,true,true,true,true,true,true] [true,true,true,true,true,true] [true,true,true,true,true,true] (.lit [true]) (.lit []) false 18,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 18,0,33⟩
def loop6 : Macro := ⟨⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.periodic [true,true] [true,true] false (.lit [])),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,16⟩
def finish6 : Macro := ⟨⟨4,(.lit [true,true]),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.lit []),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.lit [true]) (.lit []) true 8,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.lit [true]) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,10,16⟩
def G6 (n : Nat) : Z0 := ⟨4,[],[false,false,true,true,true,true,true,true,true] ++ rep Q (3*n)⟩
def F6 (k m : Nat) : Z0 := ⟨4,[true,true] ++ rep Q k,[false,false,true] ++ rep Q m⟩
theorem prepRun6 (n : Nat) : run0 p6 (18*n+33) (G6 n) = some (F6 (3*n+3) 1) := by
  have h := Macro.sound p6 prep6 (by decide) (N n 0)
  have hr : rep [true,true,true,true,true,true] n = rep Q (3*n) := by
    exact rep_mul Q 3 n
  simp only [prep6,N,PZ.eval,Word.eval] at h
  rw [hr] at h
  simpa [prep6,N,PZ.eval,Word.eval,G6,F6,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,rep_mul] using h

theorem loopRun6 (k m : Nat) : run0 p6 (10*m+16) (F6 (k+1) m) = some (F6 k (m+2)) := by
  have h := Macro.sound p6 loop6 (by decide) (N k m)
  simpa [loop6,N,PZ.eval,Word.eval,F6,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem finishRun6 (n : Nat) : run0 p6 (10*(1+2*(3*n+3))+16) (F6 0 (1+2*(3*n+3))) = some (G6 (2*n+2)) := by
  have h := Macro.sound p6 finish6 (by decide) (N 0 (1+2*(3*n+3)))
  have he : 1+2*(3*n+3) = 1+3*(2*n+2) := by omega
  simp only [finish6,N,PZ.eval,Word.eval,Nat.zero_mul,Nat.zero_add] at h
  rw [he] at h ⊢
  rw [show 1+3*(2*n+2) = 3*(2*n+2)+1 by omega] at h ⊢
  simpa [finish6,N,PZ.eval,Word.eval,F6,G6,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

def cost6 (n : Nat) : Nat := (18*n+33)+drainCost 10 16 2 (3*n+3) 1+(10*(1+2*(3*n+3))+16)
theorem growth6 (n : Nat) : run0 p6 (cost6 n) (G6 n) = some (G6 (2*n+2)) := by
  exact join0 (join0 (prepRun6 n) (drain p6 F6 10 16 2 loopRun6 (3*n+3) 1)) (finishRun6 n)
theorem first6 : run0 p6 48 ⟨0,[],[]⟩ = some (G6 0) := by decide
theorem costPositive6 (n : Nat) : 0 < cost6 n := by unfold cost6; omega
#print axioms growth6
theorem never6 (m : Machine) (hm : compatible p6 m) : NeverHalts m := never_of_map p6 G6 (fun n => 2*n+2) cost6 48 0 first6 costPositive6 growth6 m hm

def p10 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => none
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none
def prep10 : Macro := ⟨⟨4,(.lit []),(.periodic [false,false,true,true,true] [true,true] false (.lit []))⟩, ⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.lit [false,false,true,true,true])⟩, [
    .step,
    .step,
    .step,
    .step,
    .right [true] [true] [true,true] [true,true] (.lit [true,true,true,true]) (.lit []) false 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 2,0,15⟩
def loop10 : Macro := ⟨⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.periodic [true,true] [true,true] false (.lit [])),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 6,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,8,14⟩
def finish10 : Macro := ⟨⟨4,(.lit [true,true]),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.lit []),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.lit [true]) (.lit []) true 6,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.lit [true]) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,8,14⟩
def G10 (n : Nat) : Z0 := ⟨4,[],[false,false,true,true,true] ++ rep Q (1*n)⟩
def F10 (k m : Nat) : Z0 := ⟨4,[true,true] ++ rep Q k,[false,false,true] ++ rep Q m⟩
theorem prepRun10 (n : Nat) : run0 p10 (2*n+15) (G10 n) = some (F10 (1*n+1) 1) := by
  have h := Macro.sound p10 prep10 (by decide) (N n 0)
  simpa [prep10,N,PZ.eval,Word.eval,G10,F10,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,rep_mul] using h

theorem loopRun10 (k m : Nat) : run0 p10 (8*m+14) (F10 (k+1) m) = some (F10 k (m+2)) := by
  have h := Macro.sound p10 loop10 (by decide) (N k m)
  simpa [loop10,N,PZ.eval,Word.eval,F10,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem finishRun10 (n : Nat) : run0 p10 (8*(1+2*(1*n+1))+14) (F10 0 (1+2*(1*n+1))) = some (G10 (2*n+4)) := by
  have h := Macro.sound p10 finish10 (by decide) (N 0 (1+2*(1*n+1)))
  unfold G10
  rw [show 1*(2*n+4) = (1)+(1+2*(1*n+1)) by omega, ← Auto.rep_add]
  simpa [finish10,N,PZ.eval,Word.eval,F10,G10,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

def cost10 (n : Nat) : Nat := (2*n+15)+drainCost 8 14 2 (1*n+1) 1+(8*(1+2*(1*n+1))+14)
theorem growth10 (n : Nat) : run0 p10 (cost10 n) (G10 n) = some (G10 (2*n+4)) := by
  exact join0 (join0 (prepRun10 n) (drain p10 F10 8 14 2 loopRun10 (1*n+1) 1)) (finishRun10 n)
theorem first10 : run0 p10 42 ⟨0,[],[]⟩ = some (G10 2) := by decide
theorem costPositive10 (n : Nat) : 0 < cost10 n := by unfold cost10; omega
#print axioms growth10
theorem never10 (m : Machine) (hm : compatible p10 m) : NeverHalts m := never_of_map p10 G10 (fun n => 2*n+4) cost10 42 2 first10 costPositive10 growth10 m hm

def p11 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,4⟩)
  | 3,true => none
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none
def prep11 : Macro := ⟨⟨4,(.lit []),(.periodic [false,false,true,true,true] [true,true] false (.lit []))⟩, ⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.lit [false,false,true,true,true])⟩, [
    .step,
    .step,
    .step,
    .right [true] [true,true] [true,true] [true,true] (.lit [true,true,true]) (.lit []) false 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 2,0,15⟩
def loop11 : Macro := ⟨⟨4,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.periodic [true,true] [true,true] false (.lit [])),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 6,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.periodic [true,true,true] [true,true] false (.lit [])) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,8,14⟩
def finish11 : Macro := ⟨⟨4,(.lit [true,true]),(.periodic [false,false,true] [true,true] true (.lit []))⟩, ⟨4,(.lit []),(.periodic [false,false,true,true,true,true,true] [true,true] true (.lit []))⟩, [
    .right [true] [false,false,true] [true,true] [false,true] (.lit [true]) (.lit []) true 6,
    .step,
    .step,
    .step,
    .step,
    .step,
    .left [false,true,false,true,false,true] [] [false,true] [true,true] (.lit [true]) (.lit []) true 2,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step,
    .step
  ], 0,8,14⟩
def G11 (n : Nat) : Z0 := ⟨4,[],[false,false,true,true,true] ++ rep Q (1*n)⟩
def F11 (k m : Nat) : Z0 := ⟨4,[true,true] ++ rep Q k,[false,false,true] ++ rep Q m⟩
theorem prepRun11 (n : Nat) : run0 p11 (2*n+15) (G11 n) = some (F11 (1*n+1) 1) := by
  have h := Macro.sound p11 prep11 (by decide) (N n 0)
  simpa [prep11,N,PZ.eval,Word.eval,G11,F11,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,rep_mul] using h

theorem loopRun11 (k m : Nat) : run0 p11 (8*m+14) (F11 (k+1) m) = some (F11 k (m+2)) := by
  have h := Macro.sound p11 loop11 (by decide) (N k m)
  simpa [loop11,N,PZ.eval,Word.eval,F11,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem finishRun11 (n : Nat) : run0 p11 (8*(1+2*(1*n+1))+14) (F11 0 (1+2*(1*n+1))) = some (G11 (2*n+4)) := by
  have h := Macro.sound p11 finish11 (by decide) (N 0 (1+2*(1*n+1)))
  unfold G11
  rw [show 1*(2*n+4) = (1)+(1+2*(1*n+1)) by omega, ← Auto.rep_add]
  simpa [finish11,N,PZ.eval,Word.eval,F11,G11,Q,rep,Auto.rep_add,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

def cost11 (n : Nat) : Nat := (2*n+15)+drainCost 8 14 2 (1*n+1) 1+(8*(1+2*(1*n+1))+14)
theorem growth11 (n : Nat) : run0 p11 (cost11 n) (G11 n) = some (G11 (2*n+4)) := by
  exact join0 (join0 (prepRun11 n) (drain p11 F11 8 14 2 loopRun11 (1*n+1) 1)) (finishRun11 n)
theorem first11 : run0 p11 42 ⟨0,[],[]⟩ = some (G11 2) := by decide
theorem costPositive11 (n : Nat) : 0 < cost11 n := by unfold cost11; omega
#print axioms growth11
theorem never11 (m : Machine) (hm : compatible p11 m) : NeverHalts m := never_of_map p11 G11 (fun n => 2*n+4) cost11 42 2 first11 costPositive11 growth11 m hm

end BB6Coverage.Agent31Pump.Auto2.Raw13Double0LE
