import Agent46Auto2

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.D3Affine
open BB6Coverage Agent31Pump Auto

def p0 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨false,false,1⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => none
  | _,_ => none

def c0 : Auto.Cert := ⟨132,⟨0,(.lit []),(.periodic [true,false,true,false,false] [true,true,true,true] (.lit [true,true,true,true,true,true,true,true,true]))⟩,1,[.step,.step,.step,
  .right [true] [false,false] [true,true,true,true] [true,true,true,true] (.lit [true,true,true]) (.lit [true,true,true,true,true,true,true,true,true]) 20,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,
  .left [false,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [true,true,true,true] (.lit [true,true,true]) (.lit []) 28,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],48,143⟩
theorem checked0 : Auto.check p0 c0 = true := by decide
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m := Auto.check_never p0 c0 checked0 m hm
#print axioms never0

def p1 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => none
  | _,_ => none

def c1 : Auto.Cert := ⟨35,⟨0,(.lit []),(.periodic [true,false,true] [true,false,true,true,false,true,true,false,true,true,false,true] (.lit [true,false,true,true,false,true]))⟩,1,[.step,
  .right [true] [false,true] [true,false,true,true,false,true,true,false,true,true,false,true] [false,true,true,true,true,true,false,true,true,true,true,true] (.lit [true]) (.lit [true,false,true,true,false,true]) 12,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,
  .left [false,true,true,true,true,true,false,true,true,true,true,true] [] [false,true,true,true,true,true,false,true,true,true,true,true] [false,true,true,false,true,true,false,true,true,false,true,true] (.lit [true]) (.lit []) 28,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,
  .right [true] [false,true,true,false,true,true,false,true,true,false,true,true] [false,true,true,false,true,true,false,true,true,false,true,true] [false,true,true,true,true,true,false,true,true,true,true,true] (.lit [true]) (.lit []) 12,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,
  .left [false,false,true,true,true,true,true,false,true,true,true,true,true] [false] [false,true,true,true,true,true,false,true,true,true,true,true] [true,false,true,true,false,true,true,false,true,true,false,true] (.lit [true]) (.lit [true,false,true,true,false,true]) 28,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],80,118⟩
theorem checked1 : Auto.check p1 c1 = true := by decide
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m := Auto.check_never p1 c1 checked1 m hm
#print axioms never1


def p2 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => none
  | 4,false => none
  | 4,true => none
  | 5,false => none
  | 5,true => none
  | _,_ => none

def c2 : Auto.Cert := ⟨10,⟨0,(.lit []),(.periodic [true,false] [true,false,true,false,true,false] (.lit [true,true]))⟩,1,[.step,
  .right [true] [false] [true,false,true,false,true,false] [true,false,true,false,true,false] (.lit [true]) (.lit [true,true]) 6,
  .step,
  .step,
  .step,
  .left [true,false,true,false] [] [true,false,true,false,true,false] [true,false,true,false,true,false] (.lit [true]) (.lit []) 6,
  .step,
  .step,
  .step,
  .step,
  .step,
  .step,
  .step,
  .right [true] [false,true,false,true,false] [true,false,true,false,true,false] [true,false,true,false,true,false] (.lit [true]) (.lit []) 6,
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
  .left [false,true,false,true,false,true,false] [] [true,false,true,false,true,false] [false,true,false,true,false,true] (.lit [true]) (.lit [true]) 6,
  .step,
  .step,
  .step,
  .step,
  .step,
  .step,
  .step,
  .step,
  .step],24,32⟩
theorem checked2 : Auto.check p2 c2 = true := by decide
theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m := Auto.check_never p2 c2 checked2 m hm
#print axioms never2

end BB6Coverage.Agent31Pump.D3Affine

namespace BB6Coverage.Agent31Pump.D3Counter
open BB6Coverage Agent31Pump Auto2

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => none
  | _,_ => none

def shiftMacro : Macro := ⟨⟨0,(.lit []),(.periodic [true,false] [true,false] false (.periodic [true,true,false,true,false,true] [false,true] true (.lit [])))⟩,⟨0,(.lit []),(.periodic [true,false,true,false,true,false,true,false] [true,false] false (.periodic [true,true] [false,true] true (.lit [])))⟩,[.step,
  .right [true] [false] [true,false] [true,true] (.lit [true]) (.periodic [true,true,false,true,false,true] [false,true] true (.lit [])) false 2,
  .step,.step,.step,.step,.step,
  .left [true,true,true,true,true,true] [false] [true,true] [false,true] (.lit [true]) (.periodic [true] [false,true] true (.lit [])) false 4,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],6,0,22⟩
theorem shiftChecked : shiftMacro.check p = true := by decide

def oddMacro : Macro := ⟨⟨0,(.lit []),(.periodic [true,false] [true,false] false (.lit [true,true,false,true]))⟩,⟨0,(.lit []),(.periodic [true,false,true,false,true,false,true,false] [true,false] false (.lit [true]))⟩,[.step,
  .right [true] [false] [true,false] [true,true] (.lit [true]) (.lit [true,true,false,true]) false 2,
  .step,.step,.step,.step,.step,.step,
  .left [false,true,true,true,true,true,true] [] [true,true] [false,true] (.lit [true]) (.lit []) false 4,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],6,0,22⟩
theorem oddChecked : oddMacro.check p = true := by decide

def evenMacro : Macro := ⟨⟨0,(.lit []),(.periodic [true,false] [true,false] false (.lit [true,true]))⟩,⟨0,(.lit []),(.periodic [true,false,true,true,false,true,false,true,false,true] [false,true] false (.lit []))⟩,[.step,
  .right [true] [false] [true,false] [true,true] (.lit [true]) (.lit [true,true]) false 2,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,
  .left [false,true,true,true,true,true] [] [true,true] [false,true] (.lit [true]) (.lit [false,true]) false 4,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],6,0,26⟩
theorem evenChecked : evenMacro.check p = true := by decide

def plainMacro : Macro := ⟨⟨0,(.lit []),(.periodic [true,false] [true,false] false (.lit [true]))⟩,⟨0,(.lit []),(.periodic [true,false,true,true,false,true,false,true] [false,true] false (.lit []))⟩,[.step,
  .right [true] [false] [true,false] [true,true] (.lit [true]) (.lit [true]) false 2,
  .step,.step,.step,.step,.step,
  .left [false,true,true,true,true,true] [] [true,true] [false,true] (.lit [true]) (.lit []) false 4,
  .step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step],6,0,22⟩
theorem plainChecked : plainMacro.check p = true := by decide

inductive Phase where
  | marked (i j : Nat)
  | plain (i : Nat)

def config : Phase → Z0
  | .marked i j => ⟨0,[],[true,false] ++ rep [true,false] i ++ [true,true] ++ rep [false,true] j⟩
  | .plain i => ⟨0,[],[true,false] ++ rep [true,false] i ++ [true]⟩

def advance : Phase → Phase
  | .marked i 0 => .marked 0 (i+3)
  | .marked i 1 => .plain (i+3)
  | .marked i (j+2) => .marked (i+3) j
  | .plain i => .marked 0 (i+2)

def phaseCost : Phase → Nat
  | .marked i 0 => 6*i+26
  | .marked i (_+1) => 6*i+22
  | .plain i => 6*i+22

theorem phase_step (s : Phase) :
    run0 p (phaseCost s) (config s) = some (config (advance s)) := by
  cases s with
  | plain i =>
    simpa [plainMacro,phaseCost,config,advance,PZ.eval,Word.eval,rep,List.append_assoc] using
      (Macro.sound p plainMacro plainChecked (fun _ => i))
  | marked i j =>
    cases j with
    | zero =>
      simpa [evenMacro,phaseCost,config,advance,PZ.eval,Word.eval,rep,List.append_assoc] using
        (Macro.sound p evenMacro evenChecked (fun _ => i))
    | succ j =>
      cases j with
      | zero =>
        simpa [oddMacro,phaseCost,config,advance,PZ.eval,Word.eval,rep,List.append_assoc] using
          (Macro.sound p oddMacro oddChecked (fun _ => i))
      | succ j =>
        simpa [shiftMacro,phaseCost,config,advance,PZ.eval,Word.eval,rep,List.append_assoc] using
          (Macro.sound p shiftMacro shiftChecked (fun b => if b then j else i))

def orbit : Nat → Phase
  | 0 => .marked 0 0
  | n+1 => advance (orbit n)

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun n => config (orbit n)) 10 (fun n => phaseCost (orbit n)) _ _ _ m hm
  · decide
  · intro n
    cases h : orbit n with
    | plain i => simp [phaseCost]
    | marked i j => cases j <;> simp [phaseCost]
  · intro n
    exact phase_step (orbit n)

#print axioms phase_step
#print axioms never
end BB6Coverage.Agent31Pump.D3Counter
