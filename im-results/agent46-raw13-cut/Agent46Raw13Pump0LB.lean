import Agent46CarryPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Pump0LB
open BB6Coverage Agent31Pump
private def Q : List Bool := [true,true]
private def T : List Bool := [true,false]
private def P : List Bool := [false,true]
private def Z : List Bool := [false,false]
private def U : List Bool := [true]
private theorem repadd (W : List Bool) (a b : Nat) : rep W a ++ rep W b = rep W (a+b) := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp only [rep,List.append_assoc,ih,show a+1+b=a+b+1 by omega]
private theorem qcomm (n : Nat) : [true]++rep Q n=rep Q n++[true] := rotate true [true] n
def table0 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none
def table1 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none
def table2 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none
def table3 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none
def table4 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none
def table5 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none
def table6 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none
def table7 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none
def table8 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => none
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],[true]++rep Q (n+1)++P⟩

private theorem start1 (n : Nat) : run0 table1 3 (family n) = some ⟨4,Z,rep Q (n+1)++P⟩ := by
  unfold family
  rw [List.append_assoc]
  rfl
private theorem one1 (L R : List Bool) : run0 table1 4 ⟨4,Z++L,Q++Q++R⟩ = some ⟨4,Z++T++L,Q++R⟩ := by rfl
private theorem scan1 (n : Nat) : run0 table1 (4*n) ⟨4,Z,rep Q (n+1)++P⟩ = some ⟨4,Z++rep T n,Q++P⟩ := by
  have h := sweepR table1 4 Z Q Q T 4 one1 n [] P
  simp only [List.nil_append,List.append_nil] at h
  rw [← rep] at h
  simpa only [rep] using h
private theorem turn1 (L : List Bool) : run0 table1 14 ⟨4,Z++L,Q++P⟩ = some ⟨0,rep T 2++L,[true,false,true]⟩ := by rfl
private theorem backOne1 (L R : List Bool) : run0 table1 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem back1 (n : Nat) : run0 table1 (2*(n+2)) ⟨0,rep T (n+2),[true,false,true]⟩ = some (family (n+1)) := by
  have h := sweepL table1 0 [] [] T Q 2 backOne1 (n+2) [] [true,false,true]
  simp only [List.nil_append,List.append_nil] at h
  unfold family
  rw [show n+1+1=n+2 by omega,qcomm]
  simpa only [List.append_assoc,show [true]++P=[true,false,true] by rfl] using h

theorem grow1 (n : Nat) : run0 table1 (6*n+21) (family n) = some (family (n+1)) := by
  have h := join0 (join0 (start1 n) (scan1 n)) (turn1 (rep T n))
  rw [repadd,show 2+n=n+2 by omega] at h
  have H := join0 h (back1 n)
  simpa only [show 3+4*n+14+2*(n+2)=6*n+21 by omega] using H

theorem first1 : run0 table1 11 ⟨0,[],[]⟩ = some (family 0) := by rfl
#print axioms grow1
#print axioms first1

private theorem start2 (n : Nat) : run0 table2 3 (family n) = some ⟨4,Z,rep Q (n+1)++P⟩ := by
  unfold family
  rw [List.append_assoc]
  rfl
private theorem one2 (L R : List Bool) : run0 table2 8 ⟨4,Z++L,Q++Q++R⟩ = some ⟨4,Z++T++L,Q++R⟩ := by rfl
private theorem scan2 (n : Nat) : run0 table2 (8*n) ⟨4,Z,rep Q (n+1)++P⟩ = some ⟨4,Z++rep T n,Q++P⟩ := by
  have h := sweepR table2 4 Z Q Q T 8 one2 n [] P
  simp only [List.nil_append,List.append_nil] at h
  rw [← rep] at h
  simpa only [rep] using h
private theorem turn2 (L : List Bool) : run0 table2 14 ⟨4,Z++L,Q++P⟩ = some ⟨0,rep T 2++L,[true,false,true]⟩ := by rfl
private theorem backOne2 (L R : List Bool) : run0 table2 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem back2 (n : Nat) : run0 table2 (2*(n+2)) ⟨0,rep T (n+2),[true,false,true]⟩ = some (family (n+1)) := by
  have h := sweepL table2 0 [] [] T Q 2 backOne2 (n+2) [] [true,false,true]
  simp only [List.nil_append,List.append_nil] at h
  unfold family
  rw [show n+1+1=n+2 by omega,qcomm]
  simpa only [List.append_assoc,show [true]++P=[true,false,true] by rfl] using h

theorem grow2 (n : Nat) : run0 table2 (10*n+21) (family n) = some (family (n+1)) := by
  have h := join0 (join0 (start2 n) (scan2 n)) (turn2 (rep T n))
  rw [repadd,show 2+n=n+2 by omega] at h
  have H := join0 h (back2 n)
  simpa only [show 3+8*n+14+2*(n+2)=10*n+21 by omega] using H

theorem first2 : run0 table2 11 ⟨0,[],[]⟩ = some (family 0) := by rfl
#print axioms grow2
#print axioms first2

private theorem start3 (n : Nat) : run0 table3 3 (family n) = some ⟨4,Z,rep Q (n+1)++P⟩ := by
  unfold family
  rw [List.append_assoc]
  rfl
private theorem one3 (L R : List Bool) : run0 table3 4 ⟨4,Z++L,Q++Q++R⟩ = some ⟨4,Z++T++L,Q++R⟩ := by rfl
private theorem scan3 (n : Nat) : run0 table3 (4*n) ⟨4,Z,rep Q (n+1)++P⟩ = some ⟨4,Z++rep T n,Q++P⟩ := by
  have h := sweepR table3 4 Z Q Q T 4 one3 n [] P
  simp only [List.nil_append,List.append_nil] at h
  rw [← rep] at h
  simpa only [rep] using h
private theorem turn3 (L : List Bool) : run0 table3 18 ⟨4,Z++L,Q++P⟩ = some ⟨0,rep T 3++L,[true,false,true]⟩ := by rfl
private theorem backOne3 (L R : List Bool) : run0 table3 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem back3 (n : Nat) : run0 table3 (2*(n+3)) ⟨0,rep T (n+3),[true,false,true]⟩ = some (family (n+2)) := by
  have h := sweepL table3 0 [] [] T Q 2 backOne3 (n+3) [] [true,false,true]
  simp only [List.nil_append,List.append_nil] at h
  unfold family
  rw [show n+2+1=n+3 by omega,qcomm]
  simpa only [List.append_assoc,show [true]++P=[true,false,true] by rfl] using h

theorem grow3 (n : Nat) : run0 table3 (6*n+27) (family n) = some (family (n+2)) := by
  have h := join0 (join0 (start3 n) (scan3 n)) (turn3 (rep T n))
  rw [repadd,show 3+n=n+3 by omega] at h
  have H := join0 h (back3 n)
  simpa only [show 3+4*n+18+2*(n+3)=6*n+27 by omega] using H

theorem first3 : run0 table3 11 ⟨0,[],[]⟩ = some (family 0) := by rfl
#print axioms grow3
#print axioms first3
def family7 (n : Nat) : Z0 := ⟨0,[],[true,true,true,false]++rep Z n++[true]⟩
private theorem start7 (n : Nat) : run0 table7 5 (family7 n) = some ⟨3,T++Q,[false]++rep Z n++[true]⟩ := by
  unfold family7
  simp only [List.append_assoc]
  rfl
private theorem one7 (L R : List Bool) : run0 table7 4 ⟨3,T++L,[false]++Z++R⟩ = some ⟨3,T++T++L,[false]++R⟩ := by rfl
private theorem scan7 (n : Nat) (L : List Bool) : run0 table7 (4*n) ⟨3,T++L,[false]++rep Z n++[true]⟩ = some ⟨3,rep T (n+1)++L,P⟩ := by
  have h := sweepR table7 3 T [false] Z T 4 one7 n L [true]
  simpa only [rep,List.append_assoc,show [false]++[true]=P by rfl] using h
private theorem turn7 (L : List Bool) : run0 table7 8 ⟨3,T++L,P⟩ = some ⟨1,T++T++L,[true]⟩ := by rfl
private theorem oneBack7 (L R : List Bool) : run0 table7 2 ⟨1,T++L,R⟩ = some ⟨1,L,Z++R⟩ := by rfl
private theorem back7 (n : Nat) (L : List Bool) : run0 table7 (2*n) ⟨1,rep T n++L,[true]⟩ = some ⟨1,L,rep Z n++[true]⟩ := by
  simpa only [List.nil_append] using sweepL table7 1 [] [] T Z 2 oneBack7 n L [true]
private theorem pass7 (n : Nat) (L : List Bool) : run0 table7 (6*n+12) ⟨3,T++L,[false]++rep Z n++[true]⟩ = some ⟨1,L,rep Z (n+2)++[true]⟩ := by
  have h := scan7 n L
  rw [rep,List.append_assoc] at h
  have k := join0 h (turn7 (rep T n++L))
  have k' : run0 table7 (4*n+8) ⟨3,T++L,[false]++rep Z n++[true]⟩ = some ⟨1,rep T (n+2)++L,[true]⟩ := by
    simpa only [rep,List.append_assoc] using k
  have H := join0 k' (back7 (n+2) L)
  simpa only [show 4*n+8+2*(n+2)=6*n+12 by omega] using H
private theorem restart7 (n : Nat) : run0 table7 5 ⟨1,Q,rep Z (n+2)++[true]⟩ = some ⟨3,T++[true],[false]++rep Z (n+1)++[true]⟩ := by
  rw [rep]
  simp only [List.append_assoc]
  rfl
private theorem finish7 (n : Nat) : run0 table7 6 ⟨1,[true],rep Z (n+3)++[true]⟩ = some (family7 (n+3)) := by
  unfold family7
  simp only [rep,List.append_assoc]
  rfl

theorem grow7 (n : Nat) : run0 table7 (12*n+46) (family7 n) = some (family7 (n+3)) := by
  have h := join0 (join0 (join0 (join0 (start7 n) (pass7 n Q)) (restart7 n)) (pass7 (n+1) [true])) (by
    simpa only [show n+1+2=n+3 by omega] using finish7 n)
  simpa only [show 5+(6*n+12)+5+(6*(n+1)+12)+6=12*n+46 by omega] using h

theorem first7 : run0 table7 11 ⟨0,[],[]⟩ = some (family7 0) := by rfl
#print axioms grow7
#print axioms first7

def family8 (n : Nat) : Z0 := ⟨0,[],[true,true,true]++rep P (n+1)⟩
private theorem start8 (n : Nat) : run0 table8 5 (family8 n) = some ⟨4,Q++P,rep P (n+1)⟩ := by
  unfold family8
  rfl
private theorem one8 (L R : List Bool) : run0 table8 2 ⟨4,Q++L,P++R⟩ = some ⟨4,Q++Q++L,R⟩ := by rfl
private theorem scan8 (n : Nat) : run0 table8 (2*(n+1)) ⟨4,Q++P,rep P (n+1)⟩ = some ⟨4,rep Q (n+2)++P,[]⟩ := by
  have h := sweepR table8 4 Q [] P Q 2 one8 (n+1) P []
  simpa only [rep,List.append_assoc,List.nil_append,List.append_nil] using h
private theorem turn8 (L : List Bool) : run0 table8 6 ⟨4,Q++L,[]⟩ = some ⟨0,Q++Q++L,[true]⟩ := by rfl
private theorem oneBack8 (L R : List Bool) : run0 table8 10 ⟨0,Q++Q++L,[true]++R⟩ = some ⟨0,Q++L,[true]++P++R⟩ := by rfl
private theorem back8 (n : Nat) : run0 table8 (10*(n+2)) ⟨0,rep Q (n+3)++P,[true]⟩ = some ⟨0,Q++P,[true]++rep P (n+2)⟩ := by
  have h := sweepL table8 0 Q [true] Q P 10 oneBack8 (n+2) P []
  simpa only [rep,List.append_assoc,List.append_nil] using h
private theorem finish8 (R : List Bool) : run0 table8 14 ⟨0,Q++P,[true]++R⟩ = some ⟨0,[],[true,true,true]++P++P++R⟩ := by rfl

theorem grow8 (n : Nat) : run0 table8 (12*n+47) (family8 n) = some (family8 (n+3)) := by
  have h := join0 (start8 n) (scan8 n)
  rw [rep,List.append_assoc] at h
  have k := join0 h (turn8 (rep Q (n+1)++P))
  have k' : run0 table8 (5+2*(n+1)+6) (family8 n) = some ⟨0,rep Q (n+3)++P,[true]⟩ := by
    simpa only [rep,List.append_assoc] using k
  have H := join0 (join0 k' (back8 n)) (finish8 (rep P (n+2)))
  simpa only [family8,rep,List.append_assoc,show 5+2*(n+1)+6+10*(n+2)+14=12*n+47 by omega] using H

theorem first8 : run0 table8 11 ⟨0,[],[]⟩ = some (family8 0) := by rfl
#print axioms grow8
#print axioms first8
private def Z5 : List Bool := [false,false,false,false,false]
def R4 (k : Nat) : List Bool := [true]++rep Q (k+1)++Z5
private theorem zcomm (n : Nat) : [false]++rep Z n=rep Z n++[false] := rotate false [false] n
private theorem start4Gen (k : Nat) (L : List Bool) : run0 table4 4 ⟨0,Z++L,R4 k⟩ = some ⟨5,T++T++L,[true]++rep Q k++Z5⟩ := by
  unfold R4
  simp only [rep,List.append_assoc]
  rfl
private theorem start4Blank (k : Nat) : run0 table4 4 ⟨0,[],R4 k⟩ = some ⟨5,T++[true],[true]++rep Q k++Z5⟩ := by
  unfold R4
  simp only [rep,List.append_assoc]
  rfl
private theorem one4 (L R : List Bool) : run0 table4 2 ⟨5,[true]++L,[true]++Q++R⟩ = some ⟨5,[true]++Z++L,[true]++R⟩ := by rfl
private theorem scan4 (k : Nat) (L : List Bool) : run0 table4 (2*k) ⟨5,T++L,[true]++rep Q k++Z5⟩ = some ⟨5,T++rep Z k++L,[true]++Z5⟩ := by
  have h := sweepR table4 5 [true] [true] Q Z 2 one4 k ([false]++L) Z5
  have he : rep Z k++([false]++L)=[false]++rep Z k++L := by rw [← List.append_assoc,← zcomm]
  rw [List.append_assoc [true] (rep Z k) ([false]++L),he] at h
  simpa only [← List.append_assoc,show [true]++[false]=T by rfl] using h
private theorem turn4 (L : List Bool) : run0 table4 10 ⟨5,T++L,[true]++Z5⟩ = some ⟨0,L,R4 0⟩ := by rfl
private theorem prepare4 (k : Nat) (L : List Bool) : run0 table4 (2*k+14) ⟨0,Z++L,R4 k⟩ = some ⟨0,rep Z k++(T++L),R4 0⟩ := by
  have h := join0 (join0 (start4Gen k L) (scan4 k (T++L))) (turn4 (rep Z k++(T++L)))
  simpa only [List.append_assoc,show 4+2*k+10=2*k+14 by omega] using h
private theorem prepare4Blank (k : Nat) : run0 table4 (2*k+14) ⟨0,[],R4 k⟩ = some ⟨0,rep Z k++[true],R4 0⟩ := by
  have h := join0 (join0 (start4Blank k) (scan4 k [true])) (turn4 (rep Z k++[true]))
  simpa only [List.append_assoc,show 4+2*k+10=2*k+14 by omega] using h
private theorem finish4 (k : Nat) (L : List Bool) : run0 table4 2 ⟨0,T++L,R4 k⟩ = some ⟨0,L,R4 (k+1)⟩ := by
  unfold R4
  simp only [rep,List.append_assoc]
  rfl
private theorem finish4Blank (k : Nat) : run0 table4 2 ⟨0,[true],R4 k⟩ = some ⟨0,[],R4 (k+1)⟩ := by
  unfold R4
  simp only [rep,List.append_assoc]
  rfl

def family4 (n : Nat) : Z0 := ⟨0,[],R4 (n+1)⟩
theorem first4 : run0 table4 39 ⟨0,[],[]⟩ = some (family4 0) := by rfl
#print axioms prepare4
#print axioms prepare4Blank
#print axioms finish4
#print axioms finish4Blank
#print axioms first4
private def J : List Bool := [true,true,true]
private def W5 : List Bool := [false,true,false,true,true,false,true]
private def B5 : List Bool := [true,true,true,false,true,false,true,true]
private def C5 : List Bool := [true,true,true,true,true,true,true,false,false,false,false]
private def D5 : List Bool := [true,true,true,true,true,true,true,true,true,true,true,false,false]
def family5 (n : Nat) : Z0 := ⟨0,[],B5++rep J (3*n+1)⟩
def G5 (n : Nat) : Z0 := ⟨0,[],C5++[true]++rep J (3*n+1)⟩
def H5 (n : Nat) : Z0 := ⟨0,[],D5++[true]++rep J (3*n+1)⟩
private theorem start5 (R : List Bool) : run0 table5 9 ⟨0,[],B5++R⟩ = some ⟨5,[true]++W5,[true]++R⟩ := by rfl
private theorem one5 (L R : List Bool) : run0 table5 3 ⟨5,[true]++L,[true]++J++R⟩ = some ⟨5,[true]++J++L,[true]++R⟩ := by rfl
private theorem turn5 (L : List Bool) : run0 table5 6 ⟨5,[true]++L,[true]⟩ = some ⟨0,J++L,[true]⟩ := by rfl
private theorem oneBack5 (L R : List Bool) : run0 table5 13 ⟨0,J++J++L,[true]++R⟩ = some ⟨0,J++L,[true]++J++R⟩ := by rfl
private theorem finish5 (R : List Bool) : run0 table5 21 ⟨0,J++W5,[true]++R⟩ = some ⟨0,[],C5++[true]++R⟩ := by rfl
private theorem fg5 (n : Nat) : run0 table5 (48*n+52) (family5 n) = some (G5 n) := by
  have h0 := start5 (rep J (3*n+1))
  have h1 := sweepR table5 5 [true] [true] J J 3 one5 (3*n+1) W5 []
  simp only [List.append_nil] at h1
  have h2 := turn5 (rep J (3*n+1)++W5)
  have h3 := sweepL table5 0 J [true] J J 13 oneBack5 (3*n+1) W5 []
  simp only [List.append_nil] at h3
  have h := join0 (join0 (join0 (join0 h0 h1) h2) (by simpa only [List.append_assoc] using h3)) (finish5 (rep J (3*n+1)))
  simpa only [family5,G5,show 9+3*(3*n+1)+6+13*(3*n+1)+21=48*n+52 by omega] using h
private theorem gh5 (n : Nat) : run0 table5 44 (G5 n) = some (H5 n) := by
  have h (R : List Bool) : run0 table5 44 ⟨0,[],C5++[true]++R⟩ = some ⟨0,[],D5++[true]++R⟩ := by rfl
  exact h (rep J (3*n+1))
private theorem hf5 (n : Nat) : run0 table5 71 (H5 n) = some (family5 (n+1)) := by
  have h (R : List Bool) : run0 table5 71 ⟨0,[],D5++[true]++R⟩ = some ⟨0,[],B5++rep J 3++R⟩ := by rfl
  have H := h (rep J (3*n+1))
  rw [List.append_assoc B5 (rep J 3) (rep J (3*n+1)),repadd,show 3+(3*n+1)=3*(n+1)+1 by omega] at H
  exact H

theorem grow5 (n : Nat) : run0 table5 (48*n+167) (family5 n) = some (family5 (n+1)) := by
  have h := join0 (join0 (fg5 n) (gh5 n)) (hf5 n)
  simpa only [show 48*n+52+44+71=48*n+167 by omega] using h
theorem first5 : run0 table5 42 ⟨0,[],[]⟩ = some (family5 0) := by rfl
#print axioms grow5
#print axioms first5

private def W6 : List Bool := [false,true,false,true,true,true,true,true,true,true]
private def V6 : List Bool := rep P 5
private def A6 (m : Nat) (R : List Bool) : Z0 := ⟨0,[],[true]++rep Q (m+1)++R⟩
def family6 (n : Nat) : Z0 := A6 (4*n) W6
def G6 (n : Nat) : Z0 := A6 (4*n+2) V6
private theorem start6 (m : Nat) (R : List Bool) : run0 table6 4 (A6 m R) = some ⟨5,T++[true],[true]++rep Q m++R⟩ := by
  unfold A6
  simp only [rep,List.append_assoc]
  rfl
private theorem one6 (L R : List Bool) : run0 table6 4 ⟨5,T++L,[true]++Q++R⟩ = some ⟨5,T++T++L,[true]++R⟩ := by rfl
private theorem scan6 (m : Nat) (R : List Bool) : run0 table6 (4*m) ⟨5,T++[true],[true]++rep Q m++R⟩ = some ⟨5,T++rep T m++[true],[true]++R⟩ := by
  have h := sweepR table6 5 T [true] Q T 4 one6 m [true] R
  simpa only [List.append_assoc] using h
private theorem turnF6 (L : List Bool) : run0 table6 52 ⟨5,T++L,[true]++W6⟩ = some ⟨0,T++T++L,[true]++V6⟩ := by rfl
private theorem turnG6 (L : List Bool) : run0 table6 34 ⟨5,T++L,[true]++V6⟩ = some ⟨0,T++T++L,[true]++W6⟩ := by rfl
private theorem oneBack6 (L R : List Bool) : run0 table6 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem finish6 (R : List Bool) : run0 table6 2 ⟨0,[true],R⟩ = some ⟨0,[],Q++R⟩ := by rfl
private theorem back6 (m : Nat) (R : List Bool) : run0 table6 (2*(m+2)+2) ⟨0,rep T (m+2)++[true],[true]++R⟩ = some (A6 (m+2) R) := by
  have h := sweepL table6 0 [] [] T Q 2 oneBack6 (m+2) [true] ([true]++R)
  simp only [List.nil_append] at h
  have H := join0 h (finish6 (rep Q (m+2)++([true]++R)))
  unfold A6
  rw [qcomm]
  simpa only [rep,List.append_assoc] using H
private theorem fg6 (n : Nat) : run0 table6 (24*n+62) (family6 n) = some (G6 n) := by
  have h := join0 (start6 (4*n) W6) (scan6 (4*n) W6)
  rw [List.append_assoc] at h
  have H := join0 h (turnF6 (rep T (4*n)++[true]))
  have H' : run0 table6 (4+4*(4*n)+52) (family6 n) = some ⟨0,rep T (4*n+2)++[true],[true]++V6⟩ := by
    simpa only [family6,rep,List.append_assoc] using H
  have K := join0 H' (back6 (4*n) V6)
  simpa only [G6,show 4+4*(4*n)+52+(2*(4*n+2)+2)=24*n+62 by omega] using K
private theorem gf6 (n : Nat) : run0 table6 (24*n+56) (G6 n) = some (family6 (n+1)) := by
  have h := join0 (start6 (4*n+2) V6) (scan6 (4*n+2) V6)
  rw [List.append_assoc] at h
  have H := join0 h (turnG6 (rep T (4*n+2)++[true]))
  have H' : run0 table6 (4+4*(4*n+2)+34) (G6 n) = some ⟨0,rep T (4*n+2+2)++[true],[true]++W6⟩ := by
    simpa only [G6,rep,List.append_assoc] using H
  have K := join0 H' (back6 (4*n+2) W6)
  rw [show 4+4*(4*n+2)+34+(2*(4*n+2+2)+2)=24*n+56 by omega] at K
  simpa only [family6,show 4*n+2+2=4*(n+1) by omega] using K

theorem grow6 (n : Nat) : run0 table6 (48*n+118) (family6 n) = some (family6 (n+1)) := by
  have h := join0 (fg6 n) (gf6 n)
  simpa only [show 24*n+62+(24*n+56)=48*n+118 by omega] using h
theorem first6 : run0 table6 66 ⟨0,[],[]⟩ = some (family6 0) := by rfl
#print axioms grow6
#print axioms first6
private def B0 : List Bool := [false,true,false,false,true,false,false]
private def C0 : List Bool := [true,true,true,true,true,false,false]
private def Fword0 : List Bool := [true,true,true,false,false,false,true,false,false,true,false,false]
private def Gword0 : List Bool := [true,true,true,false,true,false,false,true,false,false,true,false,false]
private def Rframe0 : List Bool := [true,true,true,true,true,false,true,false]
private def Lframe0 : List Bool := [true,true,true,true,true,true,false,false]
private def Lbase0 : List Bool := [true,true,true,false,false]
private def Rbase0 : List Bool := [true,false,false]
private def Mid0 : List Bool := [true,true,true,false,false,true,false,false]
def family0 (n : Nat) : Z0 := ⟨0,[],Fword0++rep B0 (n+1)⟩
def G0 (n : Nat) : Z0 := ⟨0,[],Gword0++rep B0 (n+1)⟩
private theorem fg0 (n : Nat) : run0 table0 25 (family0 n) = some (G0 n) := by
  have h (R : List Bool) : run0 table0 25 ⟨0,[],Fword0++R⟩ = some ⟨0,[],Gword0++R⟩ := by rfl
  exact h (rep B0 (n+1))
private theorem start0 (R : List Bool) : run0 table0 31 ⟨0,[],Gword0++B0++R⟩ = some ⟨0,[false]++Lbase0,Rframe0++B0++R⟩ := by rfl
private theorem one0 (L R : List Bool) : run0 table0 33 ⟨0,[false]++L,(Rframe0++B0)++B0++R⟩ = some ⟨0,[false]++C0++L,(Rframe0++B0)++R⟩ := by rfl
private theorem last0 (L : List Bool) : run0 table0 33 ⟨0,[false]++L,Rframe0++B0⟩ = some ⟨0,[false]++C0++L,Rframe0++[false]⟩ := by rfl
private theorem scan0 (n : Nat) (L : List Bool) : run0 table0 (33*n+33) ⟨0,[false]++L,Rframe0++rep B0 (n+1)⟩ = some ⟨0,[false]++rep C0 (n+1)++L,Rframe0++[false]⟩ := by
  have h := sweepR table0 0 [false] (Rframe0++B0) B0 C0 33 one0 n L []
  simp only [List.append_nil,List.append_assoc] at h
  have H := join0 h (last0 (rep C0 n++L))
  simpa only [rep,List.append_assoc] using H
private theorem turn0 (L : List Bool) : run0 table0 17 ⟨0,[false]++L,Rframe0++[false]⟩ = some ⟨0,Lframe0++L,Rbase0⟩ := by rfl
private theorem oneBack0 (L R : List Bool) : run0 table0 21 ⟨0,Lframe0++C0++L,Rbase0++R⟩ = some ⟨0,Lframe0++L,Rbase0++B0++R⟩ := by rfl
private theorem pass0 (n : Nat) (L : List Bool) : run0 table0 (54*n+71) ⟨0,[false]++L,Rframe0++rep B0 (n+1)⟩ = some ⟨0,Lframe0++L,Rbase0++rep B0 (n+1)⟩ := by
  have h0 := scan0 n L
  rw [List.append_assoc] at h0
  have h1 := join0 h0 (turn0 (rep C0 (n+1)++L))
  have h2 := sweepL table0 0 Lframe0 Rbase0 C0 B0 21 oneBack0 (n+1) L []
  simp only [List.append_nil] at h2
  have h := join0 h1 (by simpa only [List.append_assoc] using h2)
  simpa only [show 33*n+33+17+21*(n+1)=54*n+71 by omega] using h
private theorem base0 (R : List Bool) : run0 table0 36 ⟨0,Lframe0++Lbase0,Rbase0++R⟩ = some ⟨0,[false],Mid0++B0++R⟩ := by rfl
private theorem middle0 (R : List Bool) : run0 table0 30 ⟨0,[false],Mid0++B0++R⟩ = some ⟨0,[false],Rframe0++B0++R⟩ := by rfl
private theorem end0 (R : List Bool) : run0 table0 23 ⟨0,Lframe0,Rbase0++R⟩ = some ⟨0,[],Fword0++R⟩ := by rfl
private theorem gf0 (n : Nat) : run0 table0 (108*n+316) (G0 n) = some (family0 (n+1)) := by
  have h0 : run0 table0 31 (G0 n) = some ⟨0,[false]++Lbase0,Rframe0++rep B0 (n+1)⟩ := by
    simpa only [G0,rep,List.append_assoc] using start0 (rep B0 n)
  have h1 := join0 (join0 (join0 h0 (pass0 n Lbase0)) (base0 (rep B0 (n+1)))) (middle0 (rep B0 (n+1)))
  have h1' : run0 table0 (31+(54*n+71)+36+30) (G0 n) = some ⟨0,[false],Rframe0++rep B0 (n+1+1)⟩ := by
    simpa only [rep,List.append_assoc] using h1
  have h2 := pass0 (n+1) []
  simp only [List.append_nil] at h2
  have h := join0 (join0 h1' h2) (end0 (rep B0 (n+1+1)))
  simpa only [family0,show 31+(54*n+71)+36+30+(54*(n+1)+71)+23=108*n+316 by omega] using h

theorem grow0 (n : Nat) : run0 table0 (108*n+341) (family0 n) = some (family0 (n+1)) := by
  have h := join0 (fg0 n) (gf0 n)
  simpa only [show 25+(108*n+316)=108*n+341 by omega] using h
theorem first0 : run0 table0 344 ⟨0,[],[]⟩ = some (family0 0) := by rfl
#print axioms grow0
#print axioms first0

theorem grow4 (n : Nat) : run0 table4 (Carry.cost 16 (n+1)) (family4 n) = some (family4 (n+1)) := by
  exact Carry.blank table4 0 Z T [true] R4 14 2 prepare4 finish4 prepare4Blank finish4Blank (n+1)

private theorem neverStep (p : PartialMachine) (f : Nat → Z0) (d entry : Nat) (cost : Nat → Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (f 0))
    (positive : ∀ k, 0 < cost k)
    (growth : ∀ k, run0 p (cost k) (f k) = some (f (k+d)))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun i => f (i*d)) entry (fun i => cost (i*d)) _ _ _ m hm
  · simpa only [Nat.zero_mul] using first
  · intro i; exact positive _
  · intro i
    simpa only [Nat.add_mul,Nat.one_mul] using growth (i*d)

def table (v : Nat) : PartialMachine :=
  match v with
  | 0 => table0
  | 1 => table1
  | 2 => table2
  | 3 => table3
  | 4 => table4
  | 5 => table5
  | 6 => table6
  | 7 => table7
  | _ => table8

theorem never (v : Nat) (hv : v<9) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have h : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 ∨ v=5 ∨ v=6 ∨ v=7 ∨ v=8 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact neverStep table0 family0 1 344 (fun n => 108*n+341) first0 (fun n => by omega) grow0 m hm
  · exact neverStep table1 family 1 11 (fun n => 6*n+21) first1 (fun n => by omega) grow1 m hm
  · exact neverStep table2 family 1 11 (fun n => 10*n+21) first2 (fun n => by omega) grow2 m hm
  · exact neverStep table3 family 2 11 (fun n => 6*n+27) first3 (fun n => by omega) grow3 m hm
  · exact neverStep table4 family4 1 39 (fun n => Carry.cost 16 (n+1)) first4 (fun n => Carry.cost_pos 16 (n+1) (by decide)) grow4 m hm
  · exact neverStep table5 family5 1 42 (fun n => 48*n+167) first5 (fun n => by omega) grow5 m hm
  · exact neverStep table6 family6 1 66 (fun n => 48*n+118) first6 (fun n => by omega) grow6 m hm
  · exact neverStep table7 family7 3 11 (fun n => 12*n+46) first7 (fun n => by omega) grow7 m hm
  · exact neverStep table8 family8 3 11 (fun n => 12*n+47) first8 (fun n => by omega) grow8 m hm
#print axioms grow4
#print axioms never
end BB6Coverage.Agent31Pump.Raw13Pump0LB
