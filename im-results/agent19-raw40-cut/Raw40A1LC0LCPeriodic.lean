import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A1LC0LC
open BB6Coverage BB6Coverage.Agent31Pump
abbrev P : List Bool := [false,true]
abbrev Q : List Bool := [true,false]
abbrev W : List Bool := [true,true]
abbrev T : List Bool := W++W
abbrev V : List Bool := Q++Q
theorem repAdd (p : List Bool) (n m : Nat) : rep p (n+m)=rep p n++rep p m := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    rw [show n+1+m=(n+m)+1 by omega,rep,ih]
    simp only [rep,List.append_assoc]
theorem doubleRep (p : List Bool) (n : Nat) : rep (p++p) n=rep p (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2+2*n by omega,repAdd]
    rfl
theorem padW (n : Nat) : W++rep W (2*n)++W=rep W (2*n+2) := by
  change rep W 1++rep W (2*n)++rep W 1=rep W (2*n+2)
  rw [←repAdd,←repAdd]
  congr 1
  omega
theorem splitQ (n : Nat) : Q++rep V (n+1)++Q=rep Q (2*n+4) := by
  change rep Q 1++rep V (n+1)++rep Q 1=rep Q (2*n+4)
  rw [doubleRep,←repAdd,←repAdd]
  congr 1
  omega
namespace Leaf39
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[false],W++rep P (2*n)++W⟩
def cost (n : Nat) := 45+52*n
theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem start (R : List Bool) : run0 table 10 ⟨0,[false],W++R⟩ = some ⟨0,[false,false]++W,R⟩ := by rfl
theorem forward (L R : List Bool) : run0 table 18 ⟨0,[false,false]++L,P++R⟩ =
    some ⟨0,[false,false]++W++L,R⟩ := by rfl
theorem finish (L : List Bool) : run0 table 10 ⟨0,[false,false]++L,W⟩ = some ⟨0,[false,false]++W++L,[]⟩ := by rfl
theorem turn (L : List Bool) : run0 table 9 ⟨0,[false,false]++L,[]⟩ = some ⟨0,[false]++L,T⟩ := by rfl
theorem back (L R : List Bool) : run0 table 8 ⟨0,[false]++W++L,W++R⟩ =
    some ⟨0,[false]++L,W++P++R⟩ := by rfl
theorem epoch (n : Nat) : run0 table (cost n) (family n)=some (family (n+1)) := by
  have h1 := start (rep P (2*n)++W)
  have h2 := sweepR table 0 [false,false] [] P W 18 forward (2*n) W W
  have h3 := finish (rep W (2*n)++W)
  have h4 := turn (W++rep W (2*n)++W)
  have h5 := sweepL table 0 [false] W W P 8 back (2*n+2) [] W
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h1 h2 h3 h4 h5
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have he : W++rep W (2*n)++W=rep W (2*n+2) := padW n
  simp only [List.append_assoc] at he
  rw [he] at H
  have H := join0 H h5
  simpa only [family,cost,List.append_assoc,show 10+18*(2*n)+10+9+8*(2*n+2)=45+52*n by omega,
    show 2*(n+1)=2*n+2 by omega] using H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 cost entry (by intro n; unfold cost; omega) epoch m hm
#print axioms never
end Leaf39
namespace Leaf95
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

abbrev pre : List Bool := [true,true,true,false]
abbrev post : List Bool := [true,false,true,true]
def family (n : Nat) : Z0 := ⟨0,[false],pre++rep V n++post⟩
def cost (n : Nat) := 51+18*n
theorem entry : run0 table 42 ⟨0,[],[]⟩=some (family 0) := by rfl
theorem start (R : List Bool) : run0 table 10 ⟨0,[false],pre++R⟩ = some ⟨1,[false]++T,R⟩ := by rfl
theorem forward (L R : List Bool) : run0 table 6 ⟨1,[false]++L,V++R⟩ =
    some ⟨1,[false]++T++L,R⟩ := by rfl
theorem finish (L : List Bool) : run0 table 14 ⟨1,[false]++L,post⟩ =
    some ⟨0,[true,true,true,true,true]++L,[true,true,true]⟩ := by rfl
theorem back (L R : List Bool) : run0 table 6 ⟨0,[true]++W++L,[true]++R⟩ =
    some ⟨0,[true]++L,[true]++Q++R⟩ := by rfl
theorem last (R : List Bool) : run0 table 3 ⟨0,[true],[true]++R⟩ = some ⟨0,[false],W++R⟩ := by rfl
theorem rightEq (n : Nat) : pre++rep V (n+1)++post=W++rep Q (2*n+4)++W := by
  calc
    _ = W++(Q++rep V (n+1)++Q)++W := by simp only [List.append_assoc]; rfl
    _ = _ := by rw [splitQ]
theorem epoch (n : Nat) : run0 table (cost n) (family n)=some (family (n+1)) := by
  have h1 := start (rep V n++post)
  have h2 := sweepR table 1 [false] [] V T 6 forward n T post
  have h3 := finish (rep T n++T) 
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h1 h2 h3
  have H := join0 (join0 h1 h2) h3
  have hl : [true,true,true,true,true]++rep T n++T = [true]++rep W (2*n+4) := by
    rw [doubleRep]
    change [true]++rep W 2++rep W (2*n)++rep W 2 = _
    simp only [List.append_assoc,← repAdd]
    congr 2
    omega
  simp only [List.append_assoc] at hl H
  rw [hl] at H
  have h4 := sweepL table 0 [true] [true] W Q 6 back (2*n+4) [] W
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h4
  have h5 := last (rep Q (2*n+4)++W)
  simp only [List.append_assoc] at h5
  have H := join0 (join0 H h4) h5
  have he := rightEq n
  simp only [List.append_assoc] at he H
  rw [←he] at H
  simpa only [family,cost,List.append_assoc,show 10+6*n+14+6*(2*n+4)+3=51+18*n by omega] using H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 42 cost entry (by intro n; unfold cost; omega) epoch m hm
#print axioms never
end Leaf95
namespace Leaf118
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

abbrev pre : List Bool := [true,true,false]
abbrev post : List Bool := [true,false,true,true,true]
def family (n : Nat) : Z0 := ⟨0,[false],pre++rep V n++post⟩
def cost (n : Nat) := 37+12*n
theorem entry : run0 table 34 ⟨0,[],[]⟩=some (family 0) := by rfl
theorem start (R : List Bool) : run0 table 5 ⟨0,[false],pre++R⟩ = some ⟨1,[false]++[true,true,true],R⟩ := by rfl
theorem forward (L R : List Bool) : run0 table 4 ⟨1,[false]++L,V++R⟩ =
    some ⟨1,[false]++T++L,R⟩ := by rfl
theorem finish (L : List Bool) : run0 table 13 ⟨1,[false]++[true,true,true]++L,post⟩ =
    some ⟨0,[true,true,true,true,true,true,true,true,true]++L,[true,true,true]⟩ := by rfl
theorem back (L R : List Bool) : run0 table 4 ⟨0,[true]++W++L,R⟩ =
    some ⟨0,[true]++L,Q++R⟩ := by rfl
theorem last (R : List Bool) : run0 table 3 ⟨0,[true],R⟩ = some ⟨0,[false],[true]++R⟩ := by rfl
theorem rightEq (n : Nat) : pre++rep V (n+1)++post=[true]++rep Q (2*n+4)++[true,true,true] := by
  calc
    _ = [true]++(Q++rep V (n+1)++Q)++[true,true,true] := by simp only [List.append_assoc]; rfl
    _ = _ := by rw [splitQ]
theorem epoch (n : Nat) : run0 table (cost n) (family n)=some (family (n+1)) := by
  have h1 := start (rep V n++post)
  have h2 := sweepR table 1 [false] [] V T 4 forward n [true,true,true] post
  have h3 := finish (rep T n) 
  have he : rep T n++[true,true,true]=[true,true,true]++rep T n := by
    have eq : rep T n=rep [true] (4*n) := by
      rw [doubleRep]
      change rep ([true]++[true]) (2*n)=_
      rw [doubleRep,show 2*(2*n)=4*n by omega]
    rw [eq]
    change rep [true] (4*n)++rep [true] 3=rep [true] 3++rep [true] (4*n)
    rw [←repAdd,←repAdd,Nat.add_comm]
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h1 h2 h3
  rw [he] at h2
  have H := join0 (join0 h1 h2) h3
  have hl : [true,true,true,true,true,true,true,true,true]++rep T n = [true]++rep W (2*n+4) := by
    rw [doubleRep]
    change [true]++rep W 4++rep W (2*n) = _
    simp only [List.append_assoc,← repAdd]
    congr 2
    omega
  simp only [List.append_assoc] at hl H
  rw [hl] at H
  have h4 := sweepL table 0 [true] [] W Q 4 back (2*n+4) [] [true,true,true]
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h4
  have h5 := last (rep Q (2*n+4)++[true,true,true])
  simp only [List.append_assoc] at h5
  have H := join0 (join0 H h4) h5
  have he := rightEq n
  simp only [List.append_assoc] at he H
  rw [←he] at H
  simpa only [family,cost,List.append_assoc,show 5+4*n+13+4*(2*n+4)+3=37+12*n by omega] using H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 cost entry (by intro n; unfold cost; omega) epoch m hm
#print axioms never
end Leaf118
end BB6.Agent19Raw40.A1LC0LC
