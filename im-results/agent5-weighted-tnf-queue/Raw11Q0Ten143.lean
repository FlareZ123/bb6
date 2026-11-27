import Agent5Region143
import Agent5TailPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent31Pump.Tails.Raw11Q0Ten143
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay
open BB6Coverage.Agent31Pump.Pair143 Region143

private theorem u1 : U 1 = [true] := rfl
private theorem u2 : U 2 = [true,true] := rfl
private theorem u3 : U 3 = [true,true,true] := rfl
private theorem u4 : U 4 = [true,true,true,true] := rfl
private theorem u5 : U 5 = [true,true,true,true,true] := rfl

namespace M0
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 8,
  .steps 14,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],10,0,17⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right0 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true,true,true]))⟩,⟨0,(.periodic [true,true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true,true,true]) 15,
  .steps 22],15,0,22⟩
theorem check_right0 : check table cert_right0 = true := by decide +kernel

def cert_right3 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true]))⟩,⟨0,(.periodic [true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true]) 15,
  .steps 13],15,0,13⟩
theorem check_right3 : check table cert_right3 = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨10*n+17,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right0 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*(j+1))))
    (P (Iblock (j+1) ++ true::V k) 0 1) := by
  have he : U (5*(j+1)) = U (5*j) ++ U 5 := by
    rw [show 5*(j+1)=5*j+5 by omega,Uadd]
  refine ⟨15*j+22, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right0,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right0 check_right0 j 0 (V k) []

theorem right3 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+3)))
    (P ([true,true,true,false] ++ Iblock j ++ true::V k) 0 1) := by
  have he : U (5*j+3) = U (5*j) ++ U 3 := by
    rw [show 5*j+3=5*j+3 by omega,Uadd]
  refine ⟨15*j+13, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right3,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right3 check_right3 j 0 (V k) []

theorem right : RightI table := ⟨right0,right3⟩
theorem seed : run0 table 394 ⟨0,[],[]⟩ = some (EI 1) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := neverI left right 394 seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M0

namespace M1
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 8,
  .steps 14,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],10,0,17⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right0 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true,true,true]))⟩,⟨0,(.periodic [true,true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.steps 1,
  .right [true] [true,false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true,true,true]) 15,
  .steps 21],15,0,22⟩
theorem check_right0 : check table cert_right0 = true := by decide +kernel

def cert_right3 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true]))⟩,⟨0,(.periodic [true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.steps 1,
  .right [true] [true,false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true]) 15,
  .steps 12],15,0,13⟩
theorem check_right3 : check table cert_right3 = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨10*n+17,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right0 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*(j+1))))
    (P (Iblock (j+1) ++ true::V k) 0 1) := by
  have he : U (5*(j+1)) = U (5*j) ++ U 5 := by
    rw [show 5*(j+1)=5*j+5 by omega,Uadd]
  refine ⟨15*j+22, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right0,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right0 check_right0 j 0 (V k) []

theorem right3 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+3)))
    (P ([true,true,true,false] ++ Iblock j ++ true::V k) 0 1) := by
  have he : U (5*j+3) = U (5*j) ++ U 3 := by
    rw [show 5*j+3=5*j+3 by omega,Uadd]
  refine ⟨15*j+13, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right3,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right3 check_right3 j 0 (V k) []

theorem right : RightI table := ⟨right0,right3⟩
theorem seed : run0 table 394 ⟨0,[],[]⟩ = some (EI 1) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := neverI left right 394 seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M1

namespace M2
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨true,true,5⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 8,
  .steps 14,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],10,0,17⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right2 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true]))⟩,⟨0,(.periodic [true,true,true,false] [true,false,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [false,true,true,false,true] false (.tail [] false) (.lit [true,true]) 21,
  .steps 17],21,0,17⟩
theorem check_right2 : check table cert_right2 = true := by decide +kernel

def cert_right3 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true]))⟩,⟨0,(.periodic [true,true,true,false] [true,false,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [false,true,true,false,true] false (.tail [] false) (.lit [true,true,true]) 21,
  .steps 13],21,0,13⟩
theorem check_right3 : check table cert_right3 = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨10*n+17,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right2 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+2)))
    (P (EndWord j k) 0 1) := by
  have he : U (5*j+2) = U (5*j) ++ U 2 := by
    rw [show 5*j+2=5*j+2 by omega,Uadd]
  refine ⟨21*j+17, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right2,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right2 check_right2 j 0 (V k) []

theorem right3 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+3)))
    (P (EndWord j k) 0 1) := by
  have he : U (5*j+3) = U (5*j) ++ U 3 := by
    rw [show 5*j+3=5*j+3 by omega,Uadd]
  refine ⟨21*j+13, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right3,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right3 check_right3 j 0 (V k) []

theorem right : RightRules table := ⟨right2,right3⟩
theorem seed : run0 table 70 ⟨0,[],[]⟩ = some (O 0) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Pair143.never left right seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M2

namespace M3
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨true,true,5⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 8,
  .steps 14,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],10,0,17⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right2 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [true,true,true,true,true] false (.lit [true]))⟩,⟨0,(.periodic [true,true,true,false] [true,false,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false,true] [true,true,true,true,true] [false,true,true,false,true] false (.tail [] false) (.lit [true]) 23,
  .steps 17],23,0,17⟩
theorem check_right2 : check table cert_right2 = true := by decide +kernel

def cert_right3 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [true,true,true,true,true] false (.lit [true,true]))⟩,⟨0,(.periodic [true,true,true,false] [true,false,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false,true] [true,true,true,true,true] [false,true,true,false,true] false (.tail [] false) (.lit [true,true]) 23,
  .steps 13],23,0,13⟩
theorem check_right3 : check table cert_right3 = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨10*n+17,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right2 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+2)))
    (P (EndWord j k) 0 1) := by
  have he : U (5*j+2) = true :: (U (5*j) ++ U 1) := by
    rw [show 5*j+2=1+(5*j+1) by omega,Uadd,Uadd]
    rfl
  refine ⟨23*j+17, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right2,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right2 check_right2 j 0 (V k) []

theorem right3 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+3)))
    (P (EndWord j k) 0 1) := by
  have he : U (5*j+3) = true :: (U (5*j) ++ U 2) := by
    rw [show 5*j+3=1+(5*j+2) by omega,Uadd,Uadd]
    rfl
  refine ⟨23*j+13, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right3,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right3 check_right3 j 0 (V k) []

theorem right : RightRules table := ⟨right2,right3⟩
theorem seed : run0 table 70 ⟨0,[],[]⟩ = some (O 0) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Pair143.never left right seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M3

namespace M4
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 8,
  .steps 14,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],10,0,17⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right0 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true,true,true]))⟩,⟨0,(.periodic [true,true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true,true,true]) 15,
  .steps 22],15,0,22⟩
theorem check_right0 : check table cert_right0 = true := by decide +kernel

def cert_right3 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true]))⟩,⟨0,(.periodic [true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true]) 15,
  .steps 13],15,0,13⟩
theorem check_right3 : check table cert_right3 = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨10*n+17,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right0 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*(j+1))))
    (P (Iblock (j+1) ++ true::V k) 0 1) := by
  have he : U (5*(j+1)) = U (5*j) ++ U 5 := by
    rw [show 5*(j+1)=5*j+5 by omega,Uadd]
  refine ⟨15*j+22, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right0,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right0 check_right0 j 0 (V k) []

theorem right3 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+3)))
    (P ([true,true,true,false] ++ Iblock j ++ true::V k) 0 1) := by
  have he : U (5*j+3) = U (5*j) ++ U 3 := by
    rw [show 5*j+3=5*j+3 by omega,Uadd]
  refine ⟨15*j+13, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right3,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right3 check_right3 j 0 (V k) []

theorem right : RightI table := ⟨right0,right3⟩
theorem seed : run0 table 394 ⟨0,[],[]⟩ = some (EI 1) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := neverI left right 394 seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M4

namespace M5
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 8,
  .steps 14,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],10,0,17⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right0 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true,true,true]))⟩,⟨0,(.periodic [true,true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true,true,true]) 15,
  .steps 22],15,0,22⟩
theorem check_right0 : check table cert_right0 = true := by decide +kernel

def cert_right3 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true]))⟩,⟨0,(.periodic [true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true]) 15,
  .steps 13],15,0,13⟩
theorem check_right3 : check table cert_right3 = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨10*n+17,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right0 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*(j+1))))
    (P (Iblock (j+1) ++ true::V k) 0 1) := by
  have he : U (5*(j+1)) = U (5*j) ++ U 5 := by
    rw [show 5*(j+1)=5*j+5 by omega,Uadd]
  refine ⟨15*j+22, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right0,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right0 check_right0 j 0 (V k) []

theorem right3 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+3)))
    (P ([true,true,true,false] ++ Iblock j ++ true::V k) 0 1) := by
  have he : U (5*j+3) = U (5*j) ++ U 3 := by
    rw [show 5*j+3=5*j+3 by omega,Uadd]
  refine ⟨15*j+13, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right3,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right3 check_right3 j 0 (V k) []

theorem right : RightI table := ⟨right0,right3⟩
theorem seed : run0 table 394 ⟨0,[],[]⟩ = some (EI 1) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := neverI left right 394 seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M5

namespace M6
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.steps 1,
  .right [true] [true,false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 4,
  .steps 9,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],6,0,13⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right0 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true] false (.lit [true,true,true]))⟩,⟨0,(.periodic [true,true,false] [true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true] [true,false,true] false (.tail [] false) (.lit [true,true,true]) 13,
  .steps 20],13,0,20⟩
theorem check_right0 : check table cert_right0 = true := by decide +kernel

def cert_right1 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true] false (.lit [true,true,true,true]))⟩,⟨0,(.periodic [false,true,false,true] [true,false,true] false (.tail [] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true] [true,false,true] false (.tail [] false) (.lit [true,true,true,true]) 13,
  .steps 10],13,0,10⟩
theorem check_right1 : check table cert_right1 = true := by decide +kernel

def cert_turn : Cert := ⟨⟨0,(.tail [false,true,false,true] false),(.lit [false,false,true])⟩,⟨0,(.tail [true,false,true,true,false,true] false),(.lit [false,false,true])⟩,[.steps 14],0,0,14⟩
theorem check_turn : check table cert_turn = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨6*n+13,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right0 (k j : Nat) : Reach table (A (true::true::V k) (false::U (3*(j+1))))
    (P (IIIblock (j+1) ++ true::V k) 0 1) := by
  have he : U (3*(j+1)) = U (3*j) ++ U 3 := by
    rw [show 3*(j+1)=3*j+3 by omega,Uadd]
  refine ⟨13*j+20, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,three,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right0,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right0 check_right0 j 0 (V k) []

theorem right1 (k j : Nat) : Reach table (A (true::true::V k) (false::U (3*(j+1)+1)))
    (A ([false,true,false,true] ++ rep [true,false,true] j ++ V k) [false,false,true]) := by
  have he : U (3*(j+1)+1) = U (3*j) ++ U 4 := by
    rw [show 3*(j+1)+1=3*j+4 by omega,Uadd]
  refine ⟨13*j+10, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,three,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right1 check_right1 j 0 (V k) []

theorem turn (X : List Bool) : Reach table (A ([false,true,false,true] ++ X) [false,false,true]) (A ([true,false,true,true,false,true] ++ X) [false,false,true]) :=
  ⟨14,by simpa [A,cert_turn,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_turn check_turn 0 0 X []⟩
theorem right : RightIII table where
  right0 := right0
  right1 k j := by
    have h := turn (rep [true,false,true] j ++ V k)
    have hword : [true,false,true,true,false,true] ++ (rep [true,false,true] j ++ V k) =
        [true,false] ++ IIIblock (j+1) ++ true::V k := by
      simpa [List.append_assoc] using IIIturnWord j (V k)
    rw [hword] at h
    have h' : Reach table (A ([false,true,false,true] ++ rep [true,false,true] j ++ V k) [false,false,true])
      (P ([true,false] ++ IIIblock (j+1) ++ true::V k) 0 1) := by
      simpa [P,Z,U,rep,List.append_assoc] using h
    exact (right1 k j).trans h'
theorem seed : run0 table 148 ⟨0,[],[]⟩ = some (EIII 1) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := neverIII left right 148 seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M6

namespace M7
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 6,
  .steps 12,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],8,0,15⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right0 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true,true,true]))⟩,⟨0,(.periodic [true,true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true,true,true]) 13,
  .steps 20],13,0,20⟩
theorem check_right0 : check table cert_right0 = true := by decide +kernel

def cert_right3 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true]))⟩,⟨0,(.periodic [true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true,true,true] [true,true,true,false,true] false (.tail [] false) (.lit [true,true,true]) 13,
  .steps 11],13,0,11⟩
theorem check_right3 : check table cert_right3 = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨8*n+15,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right0 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*(j+1))))
    (P (Iblock (j+1) ++ true::V k) 0 1) := by
  have he : U (5*(j+1)) = U (5*j) ++ U 5 := by
    rw [show 5*(j+1)=5*j+5 by omega,Uadd]
  refine ⟨13*j+20, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right0,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right0 check_right0 j 0 (V k) []

theorem right3 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+3)))
    (P ([true,true,true,false] ++ Iblock j ++ true::V k) 0 1) := by
  have he : U (5*j+3) = U (5*j) ++ U 3 := by
    rw [show 5*j+3=5*j+3 by omega,Uadd]
  refine ⟨13*j+11, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right3,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right3 check_right3 j 0 (V k) []

theorem right : RightI table := ⟨right0,right3⟩
theorem seed : run0 table 352 ⟨0,[],[]⟩ = some (EI 1) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := neverI left right 352 seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M7

namespace M8
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.steps 3,
  .right [false] [true] [false,true] [false,true] false (.tail [false,true] false) (.tail [false,false] true) 2,
  .steps 5,
  .left [false,true] [] [false,true] [true,false] false (.tail [false,true] false) (.tail [false,true] true) 2,
  .steps 3],4,0,11⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 7],0,0,7⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right0 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true] false (.lit [true,true,true]))⟩,⟨0,(.periodic [true,true,false] [true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true] [true,false,true] false (.tail [] false) (.lit [true,true,true]) 11,
  .steps 18],11,0,18⟩
theorem check_right0 : check table cert_right0 = true := by decide +kernel

def cert_right1 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true] false (.lit [true,true,true,true]))⟩,⟨0,(.periodic [false,true,false,true] [true,false,true] false (.tail [] false)),(.lit [false,false,true])⟩,[.right [true,true] [false] [true,true,true] [true,false,true] false (.tail [] false) (.lit [true,true,true,true]) 11,
  .steps 8],11,0,8⟩
theorem check_right1 : check table cert_right1 = true := by decide +kernel

def cert_turn : Cert := ⟨⟨0,(.tail [false,true,false,true] false),(.lit [false,false,true])⟩,⟨0,(.tail [true,false,true,true,false,true] false),(.lit [false,false,true])⟩,[.steps 12],0,0,12⟩
theorem check_turn : check table cert_turn = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨4*n+11,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right0 (k j : Nat) : Reach table (A (true::true::V k) (false::U (3*(j+1))))
    (P (IIIblock (j+1) ++ true::V k) 0 1) := by
  have he : U (3*(j+1)) = U (3*j) ++ U 3 := by
    rw [show 3*(j+1)=3*j+3 by omega,Uadd]
  refine ⟨11*j+18, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,three,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right0,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right0 check_right0 j 0 (V k) []

theorem right1 (k j : Nat) : Reach table (A (true::true::V k) (false::U (3*(j+1)+1)))
    (A ([false,true,false,true] ++ rep [true,false,true] j ++ V k) [false,false,true]) := by
  have he : U (3*(j+1)+1) = U (3*j) ++ U 4 := by
    rw [show 3*(j+1)+1=3*j+4 by omega,Uadd]
  refine ⟨11*j+8, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,three,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right1 check_right1 j 0 (V k) []

theorem turn (X : List Bool) : Reach table (A ([false,true,false,true] ++ X) [false,false,true]) (A ([true,false,true,true,false,true] ++ X) [false,false,true]) :=
  ⟨12,by simpa [A,cert_turn,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_turn check_turn 0 0 X []⟩
theorem right : RightIII table where
  right0 := right0
  right1 k j := by
    have h := turn (rep [true,false,true] j ++ V k)
    have hword : [true,false,true,true,false,true] ++ (rep [true,false,true] j ++ V k) =
        [true,false] ++ IIIblock (j+1) ++ true::V k := by
      simpa [List.append_assoc] using IIIturnWord j (V k)
    rw [hword] at h
    have h' : Reach table (A ([false,true,false,true] ++ rep [true,false,true] j ++ V k) [false,false,true])
      (P ([true,false] ++ IIIblock (j+1) ++ true::V k) 0 1) := by
      simpa [P,Z,U,rep,List.append_assoc] using h
    exact (right1 k j).trans h'
theorem seed : run0 table 132 ⟨0,[],[]⟩ = some (EIII 1) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := neverIII left right 132 seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M8

namespace M9
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => none
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def cert_pop10 : Cert := ⟨⟨0,(.tail [true,false] false),(.tail [] true)⟩,⟨0,(.tail [] false),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop10 : check table cert_pop10 = true := by decide +kernel

def cert_pop1 : Cert := ⟨⟨0,(.lit [true]),(.tail [] true)⟩,⟨0,(.lit []),(.tail [false,true] true)⟩,[.steps 2],0,0,2⟩
theorem check_pop1 : check table cert_pop1 = true := by decide +kernel

def cert_P11gen : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.tail [true] false),(.periodic [false,true] [false,true] false (.tail [false,false,true] true))⟩,[.right [true,true] [false,true] [false,true] [false,true] false (.tail [] false) (.tail [false,false] true) 10,
  .steps 18,
  .left [false,true,false,true] [] [false,true] [true,false] false (.tail [] false) (.tail [false,true] true) 2,
  .steps 3],12,0,21⟩
theorem check_P11gen : check table cert_P11gen = true := by decide +kernel

def cert_P11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,false] true)⟩,⟨0,(.tail [true] false),(.tail [false,false,true] true)⟩,[.steps 9],0,0,9⟩
theorem check_P11base : check table cert_P11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_right0 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true,true,true]))⟩,⟨0,(.periodic [true,true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.steps 4,
  .right [true] [true] [true,true,true,true,true] [true,true,true,true,false] false (.tail [true] false) (.lit [true,true,true,true,true]) 7,
  .steps 12],7,0,16⟩
theorem check_right0 : check table cert_right0 = true := by decide +kernel

def cert_right3 : Cert := ⟨⟨0,(.tail [true,true] false),(.periodic [false] [true,true,true,true,true] false (.lit [true,true,true]))⟩,⟨0,(.periodic [true,true,true,false] [true,true,true,true,false] false (.tail [true] false)),(.lit [false,false,true])⟩,[.steps 4,
  .right [true] [true] [true,true,true,true,true] [true,true,true,true,false] false (.tail [true] false) (.lit [true,true,true]) 7,
  .steps 13],7,0,17⟩
theorem check_right3 : check table cert_right3 = true := by decide +kernel

theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨9,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n => exact ⟨12*n+21,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n => exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem right0 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*(j+1))))
    (P (Iblock (j+1) ++ true::V k) 0 1) := by
  have he : U (5*(j+1)) = U (5*j) ++ U 5 := by
    rw [show 5*(j+1)=5*j+5 by omega,Uadd]
  refine ⟨7*j+16, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right0,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right0 check_right0 j 0 (V k) []

theorem right3 (k j : Nat) : Reach table (A (true::true::V k) (false::U (5*j+3)))
    (P ([true,true,true,false] ++ Iblock j ++ true::V k) 0 1) := by
  have he : U (5*j+3) = U (5*j) ++ U 3 := by
    rw [show 5*j+3=5*j+3 by omega,Uadd]
  refine ⟨7*j+17, ?_⟩
  rw [he]
  simpa [A,P,Z,rep,five,u1,u2,u3,u4,u5,Iblock,IIIblock,EndWord,B,cert_right3,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_right3 check_right3 j 0 (V k) []

theorem right : RightI table := ⟨right0,right3⟩
theorem seed : run0 table 468 ⟨0,[],[]⟩ = some (EI 1) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := neverI left right 468 seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end M9

end BB6Coverage.Agent31Pump.Tails.Raw11Q0Ten143
