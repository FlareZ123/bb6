import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Pump0LC
open BB6Coverage Agent31Pump
def table0 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,2⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none
def table1 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,2⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => none
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none
def table3 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,2⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => none
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none
def table4 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,2⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => none
  | 5,true => some (some ⟨true,false,3⟩)
  | _,_ => none
private def U (n : Nat) : List Bool := List.replicate n true
private def Q : List Bool := [true,true]
private def T : List Bool := [true,false]
private def P : List Bool := [false,true]
private theorem uadd (a b : Nat) : U a ++ U b = U (a+b) := List.replicate_append_replicate
private theorem ucons (n : Nat) : [true] ++ U n = U (n+1) := by rfl
private theorem usnoc (n : Nat) : U n ++ [true] = U (n+1) := by exact List.replicate_succ'.symm
private theorem repQ (n : Nat) : rep Q n = U (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show Q=U 2 by rfl,uadd,show 2+2*n=2*(n+1) by omega]
private theorem repTadd (a b : Nat) : rep T a ++ rep T b = rep T (a+b) := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp only [rep,List.append_assoc,ih,show a+1+b=a+b+1 by omega]
private theorem ucut (a b : Nat) : U (a+b) = U a ++ U b := (uadd a b).symm

def family1 (n : Nat) : Z0 := ⟨0,[],U (2*(n+2))⟩
private theorem start1 (n : Nat) : run0 table1 3 (family1 n) = some ⟨4,[false,false],U (2*n+3)⟩ := by
  unfold family1
  rw [show 2*(n+2)=(2*n+3)+1 by omega,← ucons]
  rfl
private theorem one1 (L R : List Bool) : run0 table1 16 ⟨4,[false,false]++L,[true,true,true]++Q++R⟩ = some ⟨4,[false,false]++T++L,[true,true,true]++R⟩ := by rfl
private theorem scan1 (n : Nat) : run0 table1 (16*n) ⟨4,[false,false],U (2*n+3)⟩ = some ⟨4,[false,false]++rep T n,[true,true,true]⟩ := by
  have h := sweepR table1 4 [false,false] [true,true,true] Q T 16 one1 n [] []
  simp only [List.append_nil] at h
  rw [repQ,show [true,true,true]=U 3 by rfl,uadd,show 3+2*n=2*n+3 by omega] at h
  exact h
private theorem end1 (L : List Bool) : run0 table1 14 ⟨4,[false,false]++L,[true,true,true]⟩ = some ⟨0,rep T 3++L,[true,true]⟩ := by rfl
private theorem aLeft1 (L R : List Bool) : run0 table1 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem back1 (n : Nat) : run0 table1 (2*(n+3)) ⟨0,rep T (n+3),[true,true]⟩ = some (family1 (n+2)) := by
  have h := sweepL table1 0 [] [] T Q 2 aLeft1 (n+3) [] [true,true]
  simp only [List.nil_append,List.append_nil,repQ] at h
  rw [show [true,true]=U 2 by rfl,uadd,show 2*(n+3)+2=2*(n+2+2) by omega] at h
  exact h

theorem grow1 (n : Nat) : run0 table1 (18*n+23) (family1 n) = some (family1 (n+2)) := by
  have h := join0 (join0 (start1 n) (scan1 n)) (end1 (rep T n))
  rw [repTadd,show 3+n=n+3 by omega] at h
  have H := join0 h (back1 n)
  simpa only [show 3+16*n+14+2*(n+3)=18*n+23 by omega] using H

def family3 (n : Nat) : Z0 := ⟨0,[],U (2*(n+2))⟩
private theorem start3 (n : Nat) : run0 table3 5 (family3 n) = some ⟨4,[true,true,true,true],U (2*n+1)⟩ := by
  unfold family3
  rw [show 2*(n+2)=3+(2*n+1) by omega,ucut]
  rfl
private theorem one3 (L R : List Bool) : run0 table3 2 ⟨4,[true,true]++L,[true]++Q++R⟩ = some ⟨4,[true,true]++P++L,[true]++R⟩ := by rfl
private theorem scan3 (n : Nat) : run0 table3 (2*n) ⟨4,[true,true,true,true],U (2*n+1)⟩ = some ⟨4,[true,true]++rep P n++[true,true],[true]⟩ := by
  have h := sweepR table3 4 [true,true] [true] Q P 2 one3 n [true,true] []
  simp only [List.append_nil,repQ,ucons] at h
  exact h
private theorem end3 (L : List Bool) : run0 table3 7 ⟨4,[true,true]++L,[true]⟩ = some ⟨0,[true,false,true,false,true]++L,[true]⟩ := by rfl
private theorem aLeft3 (L R : List Bool) : run0 table3 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem aTriple3 (L R : List Bool) : run0 table3 9 ⟨0,[true,true,true]++L,[true]++R⟩ = some ⟨0,L,[true,true,true,true]++R⟩ := by rfl
private theorem back3 (n : Nat) : run0 table3 (2*(n+2)+9) ⟨0,rep T (n+2)++[true,true,true],[true]⟩ = some (family3 (n+2)) := by
  have h := sweepL table3 0 [] [] T Q 2 aLeft3 (n+2) [true,true,true] [true]
  simp only [List.nil_append,repQ,usnoc] at h
  rw [← ucons] at h
  have g := aTriple3 [] (U (2*(n+2)))
  have H := join0 h g
  rw [show [true,true,true,true]=U 4 by rfl,uadd,show 4+2*(n+2)=2*(n+2+2) by omega] at H
  exact H

theorem grow3 (n : Nat) : run0 table3 (4*n+25) (family3 n) = some (family3 (n+2)) := by
  have h := join0 (join0 (start3 n) (scan3 n)) (end3 (rep P n++[true,true]))
  have hl : [true,false,true,false,true]++(rep P n++[true,true])=rep T (n+2)++[true,true,true] := by
    calc
      _ = rep T 2 ++ ([true] ++ rep P n) ++ [true,true] := by simp only [List.append_assoc]; rfl
      _ = rep T 2 ++ (rep T n ++ [true]) ++ [true,true] := by rw [show [true]++rep P n=rep T n++[true] from rotate true [false] n]
      _ = _ := by rw [← List.append_assoc (rep T 2) (rep T n) [true],repTadd,show 2+n=n+2 by omega]; simp only [List.append_assoc]; rfl
  rw [hl] at h
  have H := join0 h (back3 n)
  simpa only [show 5+2*n+7+(2*(n+2)+9)=4*n+25 by omega] using H

theorem first1 : run0 table1 41 ⟨0,[],[]⟩ = some (family1 2) := by rfl
theorem first3 : run0 table3 20 ⟨0,[],[]⟩ = some (family3 1) := by rfl
#print axioms grow1
#print axioms grow3
#print axioms first1
#print axioms first3
private def J : List Bool := [true,true,true]
private theorem repJ (n : Nat) : rep J n = U (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show J=U 3 by rfl,uadd,show 3+3*n=3*(n+1) by omega]
private theorem repU (n : Nat) : rep [true] n = U n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,ucons]
private theorem start0 (m : Nat) : run0 table0 4 ⟨0,[],U (m+2)++[false]⟩ = some ⟨5,[true,true,false],U m++[false]⟩ := by
  rw [show m+2=2+m by omega,ucut, List.append_assoc]
  rfl
private theorem start0z (m : Nat) : run0 table0 4 ⟨0,[false],U (m+2)++[false]⟩ = some ⟨5,[true,true,false],U m++[false]⟩ := by
  rw [show m+2=2+m by omega,ucut,List.append_assoc]
  rfl
private theorem fRight0 (L R : List Bool) : run0 table0 1 ⟨5,[true]++L,[true]++R⟩ = some ⟨5,[true]++[true]++L,R⟩ := by rfl
private theorem turn0 (L : List Bool) : run0 table0 4 ⟨5,[true]++L,[false]⟩ = some ⟨0,[true]++L,[true,false]⟩ := by rfl
private theorem scan0 (m : Nat) : run0 table0 (m+4) ⟨5,[true,true,false],U m++[false]⟩ = some ⟨0,U (m+2)++[false],[true,false]⟩ := by
  have h := sweepR table0 5 [true] [] [true] [true] 1 fRight0 m [true,false] [false]
  simp only [Nat.one_mul,List.nil_append,repU] at h
  have H := join0 h (turn0 (U m++[true,false]))
  have e : [true]++(U m++[true,false])=U (m+2)++[false] := by
    rw [← List.append_assoc [true] (U m) [true,false],ucons]
    change U (m+1)++([true]++[false])=U (m+2)++[false]
    rw [← List.append_assoc,usnoc]
  rw [e] at H
  exact H
private theorem aTriple0 (L R : List Bool) : run0 table0 9 ⟨0,J++L,[true]++R⟩ = some ⟨0,L,[true]++J++R⟩ := by rfl
private theorem back0 (k : Nat) (L : List Bool) : run0 table0 (9*k) ⟨0,U (3*k)++L,[true,false]⟩ = some ⟨0,L,U (3*k+1)++[false]⟩ := by
  have h := sweepL table0 0 [] [true] J J 9 aTriple0 k L [false]
  simp only [List.nil_append,repJ,ucons] at h
  exact h

def family0 (n : Nat) : Z0 := ⟨0,[],U (3*(n+2))++[false]⟩
private theorem round0 (k : Nat) : run0 table0 (12*k+30) (family0 k) = some ⟨0,[false],U (3*(k+2)+1)++[false]⟩ := by
  have h := join0 (start0 (3*k+4)) (scan0 (3*k+4))
  have H := join0 h (back0 (k+2) [false])
  simpa only [family0,show 3*k+4+2=3*(k+2) by omega,show 4+(3*k+4+4)+9*(k+2)=12*k+30 by omega] using H
private theorem round0z (k : Nat) : run0 table0 (12*k+33) ⟨0,[false],U (3*(k+2)+1)++[false]⟩ = some (family0 (k+1)) := by
  have h := join0 (start0z (3*k+5)) (scan0 (3*k+5))
  have e : U (3*k+5+2)++[false]=U (3*(k+2))++[true,false] := by
    rw [show 3*k+5+2=3*(k+2)+1 by omega,← usnoc,List.append_assoc]
    rfl
  rw [e] at h
  have H := join0 h (back0 (k+2) [true,false])
  have g (R : List Bool) : run0 table0 2 ⟨0,[true,false],R⟩ = some ⟨0,[],[true,true]++R⟩ := by rfl
  have G := join0 H (g (U (3*(k+2)+1)++[false]))
  rw [← List.append_assoc,show [true,true]=U 2 by rfl,uadd] at G
  rw [← e] at G
  simpa only [family0,show 3*k+5+2=3*(k+2)+1 by omega,show 2+(3*(k+2)+1)=3*(k+1+2) by omega,show 4+(3*k+5+4)+9*(k+2)+2=12*k+33 by omega] using G

theorem grow0 (n : Nat) : run0 table0 (24*n+63) (family0 n) = some (family0 (n+1)) := by
  have h := join0 (round0 n) (round0z n)
  simpa only [show 12*n+30+(12*n+33)=24*n+63 by omega] using h

theorem first0 : run0 table0 166 ⟨0,[],[]⟩ = some (family0 2) := by rfl

def family4 (n : Nat) : Z0 := ⟨0,[],U (6*n+10)⟩
private theorem start4 (n : Nat) : run0 table4 3 (family4 n) = some ⟨4,[false,true],U (6*n+9)⟩ := by
  unfold family4
  rw [show 6*n+10=(6*n+9)+1 by omega,← ucons]
  rfl
private theorem one4 (L R : List Bool) : run0 table4 18 ⟨4,[false,true]++L,[true,true,true]++Q++R⟩ = some ⟨4,[false,true]++Q++L,[true,true,true]++R⟩ := by rfl
private theorem scan4 (n : Nat) : run0 table4 (18*(3*n+3)) ⟨4,[false,true],U (6*n+9)⟩ = some ⟨4,[false,true]++U (6*n+6),[true,true,true]⟩ := by
  have h := sweepR table4 4 [false,true] [true,true,true] Q Q 18 one4 (3*n+3) [] []
  simp only [List.append_nil,repQ] at h
  rw [show [true,true,true]=U 3 by rfl,uadd,show 3+2*(3*n+3)=6*n+9 by omega,show 2*(3*n+3)=6*n+6 by omega] at h
  exact h
private theorem turn4 (L : List Bool) : run0 table4 10 ⟨4,[false,true]++L,[true,true,true]⟩ = some ⟨0,rep T 2++[true,true]++L,[true]⟩ := by rfl
private theorem aLeft4 (L R : List Bool) : run0 table4 2 ⟨0,T++L,R⟩ = some ⟨0,L,Q++R⟩ := by rfl
private theorem aTriple4 (L R : List Bool) : run0 table4 9 ⟨0,J++L,[true]++R⟩ = some ⟨0,L,[true]++J++R⟩ := by rfl
private theorem end4 (R : List Bool) : run0 table4 17 ⟨0,[true,true],[true]++R⟩ = some ⟨0,[],[true,true,true,true,true,true]++R⟩ := by rfl

theorem grow4 (n : Nat) : run0 table4 (72*n+106) (family4 n) = some (family4 (n+1)) := by
  have h := join0 (join0 (start4 n) (scan4 n)) (turn4 (U (6*n+6)))
  have e : rep T 2++[true,true]++U (6*n+6)=rep T 2++U (6*n+8) := by
    rw [List.append_assoc,show [true,true]=U 2 by rfl,uadd,show 2+(6*n+6)=6*n+8 by omega]
  rw [e] at h
  have h1 := sweepL table4 0 [] [] T Q 2 aLeft4 2 (U (6*n+8)) [true]
  simp only [List.nil_append] at h1
  have H := join0 h h1
  have h2 := sweepL table4 0 [] [true] J J 9 aTriple4 (2*n+2) [true,true] [true,true,true,true]
  simp only [List.nil_append,repJ] at h2
  have e2 : U (3*(2*n+2))++[true,true]=U (6*n+8) := by
    rw [show [true,true]=U 2 by rfl,uadd,show 3*(2*n+2)+2=6*n+8 by omega]
  rw [e2] at h2
  have H2 := join0 H h2
  have G := join0 H2 (end4 (U (3*(2*n+2))++[true,true,true,true]))
  have e3 : [true,true,true,true,true,true]++(U (3*(2*n+2))++[true,true,true,true])=U (6*(n+1)+10) := by
    rw [show [true,true,true,true,true,true]=U 6 by rfl,show [true,true,true,true]=U 4 by rfl,uadd,uadd,show 6+(3*(2*n+2)+4)=6*(n+1)+10 by omega]
  rw [e3] at G
  simpa only [family4,show 3+18*(3*n+3)+10+2*2+9*(2*n+2)+17=72*n+106 by omega] using G

theorem first4 : run0 table4 66 ⟨0,[],[]⟩ = some (family4 0) := by rfl
#print axioms grow0
#print axioms grow4
#print axioms first0
#print axioms first4
def table2 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,2⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none
private def X : List Bool := [false,false,true]
private def I : List Bool := X++Q
private def O : List Bool := [false,true,true,false,true]
private def V : List Bool := Q++X
private def frame : List Bool := [true,true,false,true]
private theorem block_rotate (X Y : List Bool) (n : Nat) : X++rep (Y++X) n=rep (X++Y) n++X := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    simp only [rep,List.append_assoc]
    rw [← List.append_assoc X Y (X++rep (Y++X) n),List.append_assoc X Y,ih]
private theorem start2 (R : List Bool) : run0 table2 7 ⟨0,[],J++I++R⟩ = some ⟨5,[false]++O,J++R⟩ := by rfl
private theorem right2 (L R : List Bool) : run0 table2 7 ⟨5,[false]++L,J++I++R⟩ = some ⟨5,[false]++O++L,J++R⟩ := by rfl
private theorem scan2 (n : Nat) (R : List Bool) : run0 table2 (7+7*n) ⟨0,[],J++rep I (n+1)++R⟩ = some ⟨5,[false]++rep O (n+1),J++R⟩ := by
  have h0 := start2 (rep I n++R)
  have h1 := sweepR table2 5 [false] J I O 7 right2 n O R
  simp only [List.append_assoc,rep_snoc O n] at h1
  have h := join0 h0 h1
  simpa only [rep,List.append_assoc] using h
private theorem turnF2 (L : List Bool) : run0 table2 15 ⟨5,[false]++L,J⟩ = some ⟨0,frame++L,[true]++X⟩ := by rfl
private theorem turnG2 (L : List Bool) : run0 table2 18 ⟨5,[false]++L,J++X++X⟩ = some ⟨0,frame++O++L,J⟩ := by rfl
private theorem left2 (L R : List Bool) : run0 table2 7 ⟨0,frame++O++L,[true]++R⟩ = some ⟨0,frame++L,[true]++V++R⟩ := by rfl
private theorem end2 (R : List Bool) : run0 table2 7 ⟨0,frame,[true]++R⟩ = some ⟨0,[],J++X++R⟩ := by rfl
private theorem back2 (n : Nat) (R : List Bool) : run0 table2 (7*n+7) ⟨0,frame++rep O n,[true]++R⟩ = some ⟨0,[],J++rep I n++X++R⟩ := by
  have h := sweepL table2 0 frame [true] O V 7 left2 n [] R
  simp only [List.append_nil,List.append_assoc] at h
  have g := join0 h (end2 (rep V n++R))
  have he : J++X++(rep V n++R)=J++rep I n++X++R := by
    simp only [List.append_assoc]
    rw [← List.append_assoc X (rep V n) R,show X++rep V n=rep I n++X from block_rotate X Q n]
    simp only [List.append_assoc]
  rw [he] at g
  exact g

def F2 (n : Nat) : Z0 := ⟨0,[],J++rep I n⟩
def G2 (n : Nat) : Z0 := ⟨0,[],J++rep I n++X++X⟩
theorem fg2 (n : Nat) : run0 table2 (14*n+36) (F2 (n+1)) = some (G2 (n+1)) := by
  have h := scan2 n []
  simp only [List.append_nil] at h
  have g := join0 (join0 h (turnF2 (rep O (n+1)))) (back2 (n+1) X)
  simpa only [F2,G2,show 7+7*n+15+(7*(n+1)+7)=14*n+36 by omega] using g
theorem gf2 (n : Nat) : run0 table2 (14*n+46) (G2 (n+1)) = some (F2 (n+3)) := by
  have h := scan2 n (X++X)
  simp only [List.append_assoc] at h
  have h1 := turnG2 (rep O (n+1))
  simp only [List.append_assoc] at h1
  have h2 := join0 h h1
  have h3 := back2 (n+2) Q
  have g := join0 h2 h3
  have he : J++rep I (n+2)++X++Q = J++rep I (n+3) := by
    rw [List.append_assoc (J++rep I (n+2)) X Q,List.append_assoc J (rep I (n+2)) (X++Q),show X++Q=I by rfl,rep_snoc I (n+2)]
    rfl
  rw [he] at g
  simpa only [F2,G2,List.append_assoc,show 7+7*n+18+(7*(n+2)+7)=14*n+46 by omega] using g

def family2 (n : Nat) : Z0 := F2 (2*n+1)
theorem grow2 (n : Nat) : run0 table2 (56*n+82) (family2 n) = some (family2 (n+1)) := by
  have h := join0 (fg2 (2*n)) (gf2 (2*n))
  simpa only [family2,show 14*(2*n)+36+(14*(2*n)+46)=56*n+82 by omega,show 2*n+3=2*(n+1)+1 by omega] using h
theorem first2 : run0 table2 26 ⟨0,[],[]⟩ = some (family2 0) := by rfl
#print axioms fg2
#print axioms gf2
#print axioms grow2
#print axioms first2

private theorem neverAffine (p : PartialMachine) (family : Nat → Z0)
    (a d entry : Nat) (cost : Nat → Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (family a))
    (positive : ∀ k, 0 < cost k)
    (growth : ∀ k, run0 p (cost k) (family k) = some (family (k+d)))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun i => family (a+i*d)) entry (fun i => cost (a+i*d)) _ _ _ m hm
  · simpa only [Nat.zero_mul,Nat.add_zero] using first
  · intro i; exact positive _
  · intro i
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using growth (a+i*d)

def table (v : Nat) : PartialMachine :=
  match v with
  | 0 => table0
  | 1 => table1
  | 2 => table2
  | 3 => table3
  | _ => table4

theorem never (v : Nat) (hv : v<5) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have h : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact neverAffine table0 family0 2 1 166 (fun n => 24*n+63) first0 (fun n => by omega) grow0 m hm
  · exact neverAffine table1 family1 2 2 41 (fun n => 18*n+23) first1 (fun n => by omega) grow1 m hm
  · exact neverAffine table2 family2 0 1 26 (fun n => 56*n+82) first2 (fun n => by omega) grow2 m hm
  · exact neverAffine table3 family3 1 2 20 (fun n => 4*n+25) first3 (fun n => by omega) grow3 m hm
  · exact neverAffine table4 family4 0 1 66 (fun n => 72*n+106) first4 (fun n => by omega) grow4 m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw13Pump0LC
