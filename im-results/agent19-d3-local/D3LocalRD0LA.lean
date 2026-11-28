import Agent46Auto2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.D3RD0LA
open BB6Coverage Agent31Pump Auto2

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨true,true,3⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => none
  | _,_ => none

def suff : List Bool := [false,true,false,true,false,true]

def mEntryMacro : Macro :=
  ⟨⟨0,.lit [],.periodic [true,false,true,true,false,true] [false,true] false (.lit [])⟩,
    ⟨0,.periodic [true,true,true] [true,true] false (.lit suff),.lit [true]⟩,
    List.replicate 26 .step ++
    [.right [true] [] [false,true] [true,true] (.lit suff) (.lit []) false 2] ++
    List.replicate 4 .step,2,0,30⟩
theorem mEntryChecked : mEntryMacro.check p = true := by decide

def yTailDrainMacro : Macro := ⟨⟨0,(.periodic [true,true,true] [true,true] false (.lit suff)),(.periodic [] [true,false] true (.lit [true]))⟩,⟨0,(.periodic [true] [true,true] false (.lit suff)),(.periodic [true,false,true,false] [true,false] true (.lit [true]))⟩,[.step,
  .right [true,true] [false] [true,false] [false,true] (.periodic [] [true,true] false (.lit suff)) (.lit [true]) true 4,
  .step,.step,.step,.step,.step,.step,.step,.step,
  .left [false,true,false,true,false,true] [] [false,true] [false,true] (.periodic [] [true,true] false (.lit suff)) (.lit []) true 2,
  .step,.step,.step,.step,.step],0,6,14⟩
theorem yTailDrainChecked : yTailDrainMacro.check p = true := by decide

def yDrainMacro : Macro := ⟨⟨0,(.periodic [true,true,true] [true,true] false (.lit [])),(.periodic [] [true,false] true (.lit [true]))⟩,⟨0,(.periodic [true] [true,true] false (.lit [])),(.periodic [true,false,true,false] [true,false] true (.lit [true]))⟩,[.step,
  .right [true,true] [false] [true,false] [false,true] (.periodic [] [true,true] false (.lit [])) (.lit [true]) true 4,
  .step,.step,.step,.step,.step,.step,.step,.step,
  .left [false,true,false,true,false,true] [] [false,true] [false,true] (.periodic [] [true,true] false (.lit [])) (.lit []) true 2,
  .step,.step,.step,.step,.step],0,6,14⟩
theorem yDrainChecked : yDrainMacro.check p = true := by decide

def yFinishMacro : Macro :=
  ⟨⟨0,.lit ([true] ++ suff),.periodic [] [true,false] true (.lit [true])⟩,
    ⟨0,.lit [],.periodic [true,false,true,false,true,false,true,false] [true,false] true (.lit [true])⟩,
    List.replicate 8 .step,0,0,8⟩
theorem yFinishChecked : yFinishMacro.check p = true := by decide

def yEndMacro : Macro := ⟨⟨0,(.lit [true]),(.periodic [] [true,false] true (.lit [true]))⟩,⟨0,(.lit []),(.periodic [true,false] [true,false] true (.lit [true]))⟩,[.step,.step],0,0,2⟩
theorem yEndChecked : yEndMacro.check p = true := by decide

def pEntryMacro : Macro := ⟨⟨0,(.lit []),(.periodic [true,false] [true,false] false (.lit [true]))⟩,⟨0,(.periodic [true,true,true,true,true,true] [true,true] false (.lit [])),(.lit [true])⟩,[.step,
  .right [true] [false] [true,false] [true,true] (.lit [true]) (.lit [true]) false 2,
  .step,.step,.step,.step,.step,.step],2,0,7⟩
theorem pEntryChecked : pEntryMacro.check p = true := by decide

def xDrainMacro : Macro := ⟨⟨0,(.periodic [] [true,false,true,false] false (.periodic [true,true,true,true] [true,true] true (.lit []))),(.lit [true])⟩,⟨0,(.periodic [true,false,true,false] [true,false,true,false] false (.periodic [true,true] [true,true] true (.lit []))),(.lit [true])⟩,[.left [] [] [true,false,true,false] [true,false,true,false] (.periodic [true,true,true,true] [true,true] true (.lit [])) (.lit [true]) false 4,
  .step,
  .right [true,true] [false] [true,false,true,false] [false,true,false,true] (.periodic [true] [true,true] true (.lit [])) (.lit [true]) false 8,
  .step,.step,.step,.step,.step,.step,.step,.step,.step],12,0,10⟩
theorem xDrainChecked : xDrainMacro.check p = true := by decide

def xEndMacro : Macro := ⟨⟨0,(.periodic [] [true,false,true,false] false (.lit [true,true])),(.lit [true])⟩,⟨0,(.lit []),(.periodic [true,false,true,true] [false,true,false,true] false (.lit []))⟩,[.left [] [] [true,false,true,false] [true,false,true,false] (.lit [true,true]) (.lit [true]) false 4,
  .step,.step,.step,.step,.step,.step,.step],4,0,7⟩
theorem xEndChecked : xEndMacro.check p = true := by decide

def markedR (j : Nat) : Z0 := ⟨0,[],[true,false,true,true] ++ rep [false,true] j⟩
def mConfig (n : Nat) : Z0 := markedR (n+1)
def pConfig (n : Nat) : Z0 := ⟨0,[],[true,false] ++ rep [true,false] n ++ [true]⟩
def yConfig (L : List Bool) (m k : Nat) : Z0 :=
  ⟨0,[true] ++ rep [true,true] m ++ L,rep [true,false] k ++ [true]⟩
def xConfig (m l : Nat) : Z0 :=
  ⟨0,rep [true,false,true,false] m ++ [true,true] ++ rep [true,true] l,[true]⟩

theorem mEntry (n : Nat) :
    run0 p (2*n+30) (mConfig n) = some (yConfig suff (n+1) 0) := by
  simpa [mEntryMacro,mConfig,markedR,yConfig,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p mEntryMacro mEntryChecked (fun _ => n))

theorem yTailStep (m k : Nat) :
    run0 p (6*k+14) (yConfig suff (m+1) k) = some (yConfig suff m (k+2)) := by
  simpa [yTailDrainMacro,yConfig,suff,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p yTailDrainMacro yTailDrainChecked (fun v => if v then k else m))

theorem yStep (m k : Nat) :
    run0 p (6*k+14) (yConfig [] (m+1) k) = some (yConfig [] m (k+2)) := by
  simpa [yDrainMacro,yConfig,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p yDrainMacro yDrainChecked (fun v => if v then k else m))

theorem yTailAll (m k : Nat) :
    run0 p (drainCost 6 14 2 m k) (yConfig suff m k) = some (yConfig suff 0 (k+2*m)) :=
  drain p (yConfig suff) 6 14 2 yTailStep m k

theorem yAll (m k : Nat) :
    run0 p (drainCost 6 14 2 m k) (yConfig [] m k) = some (yConfig [] 0 (k+2*m)) :=
  drain p (yConfig []) 6 14 2 yStep m k

theorem yFinish (k : Nat) :
    run0 p 8 (yConfig suff 0 k) = some (pConfig (k+3)) := by
  simpa [yFinishMacro,yConfig,pConfig,suff,PZ.eval,Word.eval,rep,List.append_assoc,
    show k+3 = k+1+1+1 by omega] using
    (Macro.sound p yFinishMacro yFinishChecked (fun _ => k))

theorem yEndChecked : yEndMacro.check p = true := by decide

def pEntryMacro : Macro := ⟨⟨0,(.lit []),(.periodic [true,false] [true,false] false (.lit [true]))⟩,⟨0,(.periodic [true,true,true,true,true,true] [true,true] false (.lit [])),(.lit [true])⟩,[.step,
  .right [true] [false] [true,false] [true,true] (.lit [true]) (.lit [true]) false 2,
  .step,.step,.step,.step,.step,.step],2,0,7⟩
theorem pEntryChecked : pEntryMacro.check p = true := by decide

def xDrainMacro : Macro := ⟨⟨0,(.periodic [] [true,false,true,false] false (.periodic [true,true,true,true] [true,true] true (.lit []))),(.lit [true])⟩,⟨0,(.periodic [true,false,true,false] [true,false,true,false] false (.periodic [true,true] [true,true] true (.lit []))),(.lit [true])⟩,[.left [] [] [true,false,true,false] [true,false,true,false] (.periodic [true,true,true,true] [true,true] true (.lit [])) (.lit [true]) false 4,
  .step,
  .right [true,true] [false] [true,false,true,false] [false,true,false,true] (.periodic [true] [true,true] true (.lit [])) (.lit [true]) false 8,
  .step,.step,.step,.step,.step,.step,.step,.step,.step],12,0,10⟩
theorem xDrainChecked : xDrainMacro.check p = true := by decide

def xEndMacro : Macro := ⟨⟨0,(.periodic [] [true,false,true,false] false (.lit [true,true])),(.lit [true])⟩,⟨0,(.lit []),(.periodic [true,false,true,true] [false,true,false,true] false (.lit []))⟩,[.left [] [] [true,false,true,false] [true,false,true,false] (.lit [true,true]) (.lit [true]) false 4,
  .step,.step,.step,.step,.step,.step,.step],4,0,7⟩
theorem xEndChecked : xEndMacro.check p = true := by decide

def markedR (j : Nat) : Z0 := ⟨0,[],[true,false,true,true] ++ rep [false,true] j⟩
def mConfig (n : Nat) : Z0 := markedR (n+1)
def pConfig (n : Nat) : Z0 := ⟨0,[],[true,false] ++ rep [true,false] n ++ [true]⟩
def yConfig (L : List Bool) (m k : Nat) : Z0 :=
  ⟨0,[true] ++ rep [true,true] m ++ L,rep [true,false] k ++ [true]⟩
def xConfig (m l : Nat) : Z0 :=
  ⟨0,rep [true,false,true,false] m ++ [true,true] ++ rep [true,true] l,[true]⟩

theorem mEntry (n : Nat) :
    run0 p (2*n+30) (mConfig n) = some (yConfig suff (n+1) 0) := by
  simpa [mEntryMacro,mConfig,markedR,yConfig,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p mEntryMacro mEntryChecked (fun _ => n))

theorem yTailStep (m k : Nat) :
    run0 p (6*k+14) (yConfig suff (m+1) k) = some (yConfig suff m (k+2)) := by
  simpa [yTailDrainMacro,yConfig,suff,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p yTailDrainMacro yTailDrainChecked (fun v => if v then k else m))

theorem yStep (m k : Nat) :
    run0 p (6*k+14) (yConfig [] (m+1) k) = some (yConfig [] m (k+2)) := by
  simpa [yDrainMacro,yConfig,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p yDrainMacro yDrainChecked (fun v => if v then k else m))

theorem yTailAll (m k : Nat) :
    run0 p (drainCost 6 14 2 m k) (yConfig suff m k) = some (yConfig suff 0 (k+2*m)) :=
  drain p (yConfig suff) 6 14 2 yTailStep m k

theorem yAll (m k : Nat) :
    run0 p (drainCost 6 14 2 m k) (yConfig [] m k) = some (yConfig [] 0 (k+2*m)) :=
  drain p (yConfig []) 6 14 2 yStep m k

theorem yCross (k : Nat) :
    run0 p 2 (yConfig suff 0 k) = some (yConfig [] 3 (k+1)) := by
  simpa [yCrossMacro,yConfig,suff,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p yCrossMacro yCrossChecked (fun _ => k))

theorem yEnd (k : Nat) :
    run0 p 2 (yConfig [] 0 k) = some (pConfig k) := by
  simpa [yEndMacro,yConfig,pConfig,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p yEndMacro yEndChecked (fun _ => k))

theorem pEntry (n : Nat) :
    run0 p (2*n+7) (pConfig n) = some (xConfig 0 (n+2)) := by
  simpa [pEntryMacro,pConfig,xConfig,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p pEntryMacro pEntryChecked (fun _ => n))

theorem xStep (m l : Nat) :
    run0 p (12*m+10) (xConfig m (l+1)) = some (xConfig (m+1) l) := by
  simpa [xDrainMacro,xConfig,PZ.eval,Word.eval,rep,List.append_assoc] using
    (Macro.sound p xDrainMacro xDrainChecked (fun v => if v then l else m))

theorem xAll (l m : Nat) :
    run0 p (drainCost 12 10 1 l m) (xConfig m l) = some (xConfig (m+l) 0) := by
  simpa using (drain p (fun l m => xConfig m l) 12 10 1 (fun l m => xStep m l) l m)

theorem xEnd (m : Nat) :
    run0 p (4*m+7) (xConfig m 0) = some (markedR (2*m)) := by
  have hrep : rep [false,true,false,true] m = rep [false,true] (2*m) := by
    simpa [rep] using (Auto2.rep_mul [false,true] 2 m)
  simpa [xEndMacro,xConfig,markedR,PZ.eval,Word.eval,rep,List.append_assoc,hrep] using
    (Macro.sound p xEndMacro xEndChecked (fun _ => m))

def mCost (n : Nat) : Nat :=
  (2*n+30) + drainCost 6 14 2 (n+1) 0 + 8

def pCost (n : Nat) : Nat :=
  (2*n+7) + drainCost 12 10 1 (n+2) 0 + (4*(n+2)+7)

theorem mReturn (n : Nat) :
    run0 p (mCost n) (mConfig n) = some (pConfig (2*n+5)) := by
  have h2 : run0 p (drainCost 6 14 2 (n+1) 0) (yConfig suff (n+1) 0) =
      some (yConfig suff 0 (2*(n+1))) := by simpa using yTailAll (n+1) 0
  have h3 : run0 p 8 (yConfig suff 0 (2*(n+1))) =
      some (pConfig (2*n+5)) := by
    simpa only [show 2*(n+1)+3 = 2*n+5 by omega] using yFinish (2*(n+1))
  exact join0 (join0 (mEntry n) h2) h3

theorem pReturn (n : Nat) :
    run0 p (pCost n) (pConfig n) = some (mConfig (2*n+3)) := by
  have h2 : run0 p (drainCost 12 10 1 (n+2) 0) (xConfig 0 (n+2)) =
      some (xConfig (n+2) 0) := by simpa using xAll (n+2) 0
  have h3 : run0 p (4*(n+2)+7) (xConfig (n+2) 0) = some (mConfig (2*n+3)) := by
    simpa only [mConfig,show 2*(n+2) = 2*n+3+1 by omega] using xEnd (n+2)
  exact join0 (join0 (pEntry n) h2) h3

inductive Phase where
  | marked (n : Nat)
  | plain (n : Nat)
def config : Phase → Z0
  | .marked n => mConfig n
  | .plain n => pConfig n
def advance : Phase → Phase
  | .marked n => .plain (2*n+5)
  | .plain n => .marked (2*n+3)
def phaseCost : Phase → Nat
  | .marked n => mCost n
  | .plain n => pCost n
theorem phase_step (s : Phase) :
    run0 p (phaseCost s) (config s) = some (config (advance s)) := by
  cases s with
  | marked n => exact mReturn n
  | plain n => exact pReturn n
def orbit : Nat → Phase
  | 0 => .plain 3
  | n+1 => advance (orbit n)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun n => config (orbit n)) 46 (fun n => phaseCost (orbit n)) _ _ _ m hm
  · decide
  · intro n
    cases h : orbit n with
    | marked k => simp only [phaseCost,mCost]; omega
    | plain k => simp only [phaseCost,pCost]; omega
  · intro n
    exact phase_step (orbit n)
#print axioms mReturn
#print axioms pReturn
#print axioms never
end BB6Coverage.Agent31Pump.D3RD0LA
