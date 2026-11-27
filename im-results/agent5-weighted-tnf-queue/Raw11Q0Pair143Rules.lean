import Agent5TailPump
import Agent5Pair143
import Agent5MultiPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent31Pump.Tails.Raw11Q0Pair143
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay
open BB6Coverage.Agent31Pump.Pair143

namespace M0
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨false,true,4⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | 5,true => none
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

def cert_Q11base : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,true] true)⟩,⟨0,(.tail [false,false,true] false),(.tail [false] true)⟩,[.steps 5],0,0,5⟩
theorem check_Q11base : check table cert_Q11base = true := by decide +kernel

def cert_initial : Cert := ⟨⟨0,(.lit []),(.periodic [false,true] [false,true] false (.tail [false,false] true))⟩,⟨0,(.periodic [true,true,true,true] [true,true] false (.lit [])),(.tail [false] true)⟩,[.steps 1,
  .right [false] [true] [false,true] [true,true] false (.lit [true]) (.tail [false,false] true) 2,
  .steps 4],2,0,5⟩
theorem check_initial : check table cert_initial = true := by decide +kernel

def cert_initialBase : Cert := ⟨⟨0,(.lit []),(.tail [false,false] true)⟩,⟨0,(.lit [true,true]),(.tail [false] true)⟩,[.steps 3],0,0,3⟩
theorem check_initialBase : check table cert_initialBase = true := by decide +kernel

def cert_R5 : Cert := ⟨⟨0,(.tail [false,false] false),(.tail [false,true,true,true,true,true] true)⟩,⟨0,(.tail [false,false,true,false,true,true,false] false),(.tail [false] true)⟩,[.steps 21],0,0,21⟩
theorem check_R5 : check table cert_R5 = true := by decide +kernel

def cert_R1 : Cert := ⟨⟨0,(.tail [false,false] false),(.lit [false,true])⟩,⟨0,(.tail [true,true,true,false] false),(.lit [false,false,true])⟩,[.steps 12],0,0,12⟩
theorem check_R1 : check table cert_R1 = true := by decide +kernel

def cert_R2 : Cert := ⟨⟨0,(.tail [false,false] false),(.lit [false,true,true])⟩,⟨0,(.tail [true,true,true,false] false),(.lit [false,false,true])⟩,[.steps 8],0,0,8⟩
theorem check_R2 : check table cert_R2 = true := by decide +kernel


theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n =>
      exact ⟨10*n+17,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n =>
      exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem q11 (X Y : List Bool) : Reach table (A (true::true::X) (false::true::Y))
    (A (false::false::true::X) (false::Y)) :=
  ⟨5,by simpa [A,cert_Q11base,PZ.eval,Word.eval] using check_sound table cert_Q11base check_Q11base 0 0 X Y⟩
theorem r5 (W Y : List Bool) : Reach table (A (false::false::W) ([false,true,true,true,true,true] ++ Y))
    (A ([false,false,true,false,true,true,false] ++ W) (false::Y)) :=
  ⟨21,by simpa [A,cert_R5,PZ.eval,Word.eval] using check_sound table cert_R5 check_R5 0 0 W Y⟩
theorem r1 (W : List Bool) : Reach table (A (false::false::W) [false,true])
    (A ([true,true,true,false] ++ W) [false,false,true]) :=
  ⟨12,by simpa [A,cert_R1,PZ.eval,Word.eval] using check_sound table cert_R1 check_R1 0 0 W []⟩
theorem r2 (W : List Bool) : Reach table (A (false::false::W) [false,true,true])
    (A ([true,true,true,false] ++ W) [false,false,true]) :=
  ⟨8,by simpa [A,cert_R2,PZ.eval,Word.eval] using check_sound table cert_R2 check_R2 0 0 W []⟩
theorem loop (j a : Nat) (W : List Bool) :
    Reach table (A (false::false::W) (false::U (5*j+a)))
      (A (false::false::(B j ++ W)) (false::U a)) := by
  induction j generalizing W with
  | zero => simpa [B,rep] using (show Reach table (A (false::false::W) (false::U a)) (A (false::false::W) (false::U a)) from ⟨0,rfl⟩)
  | succ j ih =>
    have h := r5 W (U (5*j+a))
    have he : 5*(j+1)+a = 5+(5*j+a) := by omega
    have h' : Reach table (A (false::false::W) (false::U (5*(j+1)+a)))
        (A (false::false::([true,false,true,true,false] ++ W)) (false::U (5*j+a))) := by
      rw [he,Uadd]
      simpa [U,rep] using h
    have ht := ih ([true,false,true,true,false] ++ W)
    rw [Bsnoc]
    simpa [List.append_assoc] using h'.trans ht
theorem right : RightRules table where
  right2 k j := by
    have h := q11 (V k) (U (5*j+1))
    have h' : Reach table (A (true::true::V k) (false::U (5*j+2)))
        (A (false::false::true::V k) (false::U (5*j+1))) := by
      have he : 5*j+2 = (5*j+1)+1 := by omega
      rw [he]
      simpa [U,rep] using h
    have b := loop j 1 (true::V k)
    have c := r1 (B j ++ true::V k)
    exact (h'.trans b).trans c
  right3 k j := by
    have h := q11 (V k) (U (5*j+2))
    have h' : Reach table (A (true::true::V k) (false::U (5*j+3)))
        (A (false::false::true::V k) (false::U (5*j+2))) := by
      have he : 5*j+3 = (5*j+2)+1 := by omega
      rw [he]
      simpa [U,rep] using h
    have b := loop j 2 (true::V k)
    have c := r2 (B j ++ true::V k)
    exact (h'.trans b).trans c

theorem seed : run0 table 70 ⟨0,[],[]⟩ = some (O 0) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Pair143.never left right seed m hm
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
  | 5,true => some (some ⟨false,false,1⟩)
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

def cert_R1 : Cert := ⟨⟨0,(.tail [false,false] false),(.lit [false,true])⟩,⟨0,(.tail [true,true,true,false] false),(.lit [false,false,true])⟩,[.steps 12],0,0,12⟩
theorem check_R1 : check table cert_R1 = true := by decide +kernel

def cert_R2 : Cert := ⟨⟨0,(.tail [false,false] false),(.lit [false,true,true])⟩,⟨0,(.tail [true,true,true,false] false),(.lit [false,false,true])⟩,[.steps 8],0,0,8⟩
theorem check_R2 : check table cert_R2 = true := by decide +kernel

def cert_loop : Cert := ⟨⟨0,(.tail [true,true] false),(.tail [false,true,true,true,true,true] true)⟩,⟨0,(.tail [true,true,false,true,true,false,true] false),(.tail [false] true)⟩,[.steps 23],0,0,23⟩
theorem check_loop : check table cert_loop = true := by decide +kernel

def cert_end2 : Cert := ⟨⟨0,(.tail [true,true] false),(.lit [false,true,true])⟩,⟨0,(.tail [true,true,true,false,true] false),(.lit [false,false,true])⟩,[.steps 17],0,0,17⟩
theorem check_end2 : check table cert_end2 = true := by decide +kernel

def cert_end3 : Cert := ⟨⟨0,(.tail [true,true] false),(.lit [false,true,true,true])⟩,⟨0,(.tail [true,true,true,false,true] false),(.lit [false,false,true])⟩,[.steps 13],0,0,13⟩
theorem check_end3 : check table cert_end3 = true := by decide +kernel


theorem left : LeftRules table where
  pop10 X Y := ⟨2, by simpa [A,cert_pop10,PZ.eval,Word.eval] using check_sound table cert_pop10 check_pop10 0 0 X Y⟩
  pop1 Y := ⟨2, by simpa [A,cert_pop1,PZ.eval,Word.eval] using check_sound table cert_pop1 check_pop1 0 0 [] Y⟩
  pop11 n X Y := by
    cases n with
    | zero => exact ⟨7,by simpa [A,Z,rep,cert_P11base,PZ.eval,Word.eval] using check_sound table cert_P11base check_P11base 0 0 X Y⟩
    | succ n =>
      exact ⟨10*n+17,by simpa [A,Z,rep,cert_P11gen,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_P11gen check_P11gen n 0 X Y⟩
  init n Y := by
    cases n with
    | zero => exact ⟨3,by omega,by simpa [A,Z,V,rep,cert_initialBase,PZ.eval,Word.eval] using check_sound table cert_initialBase check_initialBase 0 0 [] Y⟩
    | succ n =>
      exact ⟨2*n+5,by omega,by simpa [A,Z,V,rep,cert_initial,PZ.eval,Word.eval,List.append_assoc] using check_sound table cert_initial check_initial n 0 [] Y⟩

theorem r5 (W Y : List Bool) : Reach table (A (true::true::W) ([false,true,true,true,true,true] ++ Y))
    (A ([true,true,false,true,true,false,true] ++ W) (false::Y)) :=
  ⟨23,by simpa [A,cert_loop,PZ.eval,Word.eval] using check_sound table cert_loop check_loop 0 0 W Y⟩
theorem r2 (W : List Bool) : Reach table (A (true::true::W) [false,true,true])
    (A ([true,true,true,false,true] ++ W) [false,false,true]) :=
  ⟨17,by simpa [A,cert_end2,PZ.eval,Word.eval] using check_sound table cert_end2 check_end2 0 0 W []⟩
theorem r3 (W : List Bool) : Reach table (A (true::true::W) [false,true,true,true])
    (A ([true,true,true,false,true] ++ W) [false,false,true]) :=
  ⟨13,by simpa [A,cert_end3,PZ.eval,Word.eval] using check_sound table cert_end3 check_end3 0 0 W []⟩
theorem loop (j a : Nat) (W : List Bool) :
    Reach table (A (true::true::W) (false::U (5*j+a)))
      (A (true::true::(C j ++ W)) (false::U a)) := by
  induction j generalizing W with
  | zero => simpa [C,rep] using (show Reach table (A (true::true::W) (false::U a)) (A (true::true::W) (false::U a)) from ⟨0,rfl⟩)
  | succ j ih =>
    have h := r5 W (U (5*j+a))
    have he : 5*(j+1)+a = 5+(5*j+a) := by omega
    have h' : Reach table (A (true::true::W) (false::U (5*(j+1)+a)))
        (A (true::true::([false,true,true,false,true] ++ W)) (false::U (5*j+a))) := by
      rw [he,Uadd]
      simpa [U,rep] using h
    have ht := ih ([false,true,true,false,true] ++ W)
    rw [Csnoc]
    simpa [List.append_assoc] using h'.trans ht
theorem right : RightRules table where
  right2 k j := by
    have a := loop j 2 (V k)
    have b := r2 (C j ++ V k)
    have b' : Reach table (A (true::true::(C j ++ V k)) (false::U 2)) (P (EndWord j k) 0 1) := by
      simpa [P,EndWord,Z,U,rep,List.append_assoc,Pair143.rotate] using b
    exact a.trans b'
  right3 k j := by
    have a := loop j 3 (V k)
    have b := r3 (C j ++ V k)
    have b' : Reach table (A (true::true::(C j ++ V k)) (false::U 3)) (P (EndWord j k) 0 1) := by
      simpa [P,EndWord,Z,U,rep,List.append_assoc,Pair143.rotate] using b
    exact a.trans b'

theorem seed : run0 table 70 ⟨0,[],[]⟩ = some (O 0) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Pair143.never left right seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover

end M1

end BB6Coverage.Agent31Pump.Tails.Raw11Q0Pair143
