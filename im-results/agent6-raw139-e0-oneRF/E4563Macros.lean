import PadGrowth
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6E4563
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def E (L R : List Bool) : Z0 := ⟨4,R.headD false::L,R.tail⟩
def O (n : Nat) : List Bool := rep [true] n
def Zs (n : Nat) : List Bool := rep [false] n

theorem r01 (L T : List Bool) : run0 p 2 (E L ([false,true]++T)) = some (E ([false,true]++L) T) := by cases T <;> rfl
theorem r001 (L T : List Bool) : run0 p 3 (E L ([false,false,true]++T)) = some (E ([false,true,true]++L) T) := by cases T <;> rfl
theorem r10 (a : Bool) (L T : List Bool) : run0 p 3 (E (a::L) ([true,false]++T)) = some (E L ([a,false,true]++T)) := by cases a <;> rfl
theorem r11 (a : Bool) (L T : List Bool) : run0 p 5 (E ([false,true,a]++L) ([true,true]++T)) = some (E L ([a,false,true,false,false]++T)) := by cases a <;> rfl
theorem r00000 (L T : List Bool) : run0 p 6 (E L ([false,false,false,false,false]++T)) = some (E ([true,true]++L) ([true,false,true]++T)) := rfl
theorem r00001 (a : Bool) (L T : List Bool) : run0 p 11 (E ([false,true,a]++L) ([false,false,false,false,true]++T)) = some (E L ([a,false,true,false,false,false,false,false]++T)) := by cases a <;> rfl
theorem r000101 (L T : List Bool) : run0 p 9 (E L ([false,false,false,true,false,true]++T)) = some (E (true::L) ([true,false,true,false,false]++T)) := rfl

theorem r000On00 (n : Nat) (L T : List Bool) : run0 p (n+7) (E L ([false,false,false]++O (n+1)++[false,false]++T)) = some (E (Zs n++[true,true,true]++L) ([false,false,true]++T)) := by
  have h0 (L R : List Bool) : run0 p 3 (E L ([false,false,false,true]++R)) = some ⟨1,[true,true,true,true]++L,R⟩ := rfl
  have hloop (L R : List Bool) : run0 p 1 ⟨1,[true]++L,[true]++R⟩ = some ⟨1,[true,false]++L,R⟩ := rfl
  have h1 := sweepR p 1 [true] [] [true] [false] 1 hloop n ([true,true,true]++L) ([false,false]++T)
  have h2 (L R : List Bool) : run0 p 4 ⟨1,[true]++L,[false,false]++R⟩ = some (E L ([false,false,true]++R)) := rfl
  have h1' : run0 p n ⟨1,[true,true,true,true]++L,O n++[false,false]++T⟩ = some ⟨1,true::(Zs n++[true,true,true]++L),[false,false]++T⟩ := by
    simpa only [O,Zs,List.append_assoc,List.nil_append,List.cons_append,Nat.one_mul] using h1
  have h := join0 (join0 (h0 L (O n++[false,false]++T)) h1') (h2 (Zs n++[true,true,true]++L) T)
  simpa only [O,Zs,rep.eq_2,List.append_assoc,List.cons_append,List.nil_append,Nat.one_mul,show 3+n+4=n+7 by omega] using h

theorem sweepLeftOne (L R : List Bool) : run0 p 29 (E ([true,true,true,true,true,true,false]++L) ([true,false,true]++R)) = some (E L ([true,false,true,false,false,true,true,true,true,true]++R)) := rfl
theorem sweepRightOne (L R : List Bool) : run0 p 19 (E L ([false,false,true,true,false,false,true,true,true,true,true]++R)) = some (E ([false,true,true,true,true,true,true]++L) ([false,false,true,true]++R)) := rfl

theorem seed4 : run0 p 4 ⟨0,[],[]⟩ = some (E [] [true,false,true]) := rfl
#print axioms r000On00
#print axioms sweepLeftOne
#print axioms sweepRightOne
#print axioms seed4
end BB6.Agent6E4563
