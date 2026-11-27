import Raw43RD1Growth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43RF0M13
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent25Raw43RD1Growth
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def P : List Bool := [false,true]
def Q : List Bool := [true,false]
def U := P++P
def V := Q++Q
def T : List Bool := [false,false,false,true]
def Z : List Bool := [false,false]
def sect (n : Nat) : Z0 := ⟨0,[],rep P (2*(n+1))++[false]⟩
private theorem first : run0 table 13 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem enter (R : List Bool) : run0 table 2 ⟨0,[],P++R⟩ =
  some ⟨2,[true,true,true],R⟩ := by rfl
private theorem right (L R : List Bool) :
  run0 table 4 ⟨2,[true,true]++L,[]++U++R⟩ =
  some ⟨2,[true,true]++T++L,[]++R⟩ := by rfl
private theorem turn (L : List Bool) :
  run0 table 11 ⟨2,[true,true]++L,[false,true,false]⟩ =
  some ⟨4,rep Z 3++[true]++L,[false]⟩ := by rfl
private theorem zero (L R : List Bool) :
  run0 table 2 ⟨4,[]++Z++L,[false]++R⟩ =
  some ⟨4,[]++L,[false]++Q++R⟩ := by rfl
private theorem left (L R : List Bool) :
  run0 table 6 ⟨4,[true]++T++L,[false]++R⟩ =
  some ⟨4,[true]++L,[false]++V++R⟩ := by rfl
private theorem finish (R : List Bool) :
  run0 table 4 ⟨4,[true,true],[false]++R⟩ =
  some ⟨0,[],[false]++Q++R⟩ := by rfl
theorem grow (n : Nat) :
    run0 table (10*(n+1)+13) (sect n) = some (sect (n+1)) := by
  have he : rep P (2*(n+1)) = P++rep U n++P := by
    rw [show 2*(n+1)=1+(2*n+1) by omega,rep_add P 1 (2*n+1),rep_add P (2*n) 1,rep_double P n]
    rfl
  have h1 : run0 table 2 (sect n) =
      some ⟨2,[true,true,true],rep U n++[false,true,false]⟩ := by
    rw [sect,he]
    simpa only [P,List.append_assoc,List.cons_append,List.nil_append] using enter (rep U n++[false,true,false])
  have h2 := sweepR table 2 [true,true] [] U T 4 right n [true] [false,true,false]
  have h2' : run0 table (4*n) ⟨2,[true,true,true],rep U n++[false,true,false]⟩ =
      some ⟨2,[true,true]++rep T n++[true],[false,true,false]⟩ := by
    simpa only [List.nil_append,List.cons_append,List.append_nil] using h2
  have h3 := turn (rep T n++[true])
  have h4 := sweepL table 4 [] [false] Z Q 2 zero 3 ([true]++rep T n++[true]) []
  have h4' : run0 table 6 ⟨4,rep Z 3++[true]++(rep T n++[true]),[false]⟩ =
      some ⟨4,[true]++rep T n++[true],[false]++rep Q 3⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using h4
  have h5 := sweepL table 4 [true] [false] T V 6 left n [true] (rep Q 3)
  have h5' : run0 table (6*n) ⟨4,[true]++rep T n++[true],[false]++rep Q 3⟩ =
      some ⟨4,[true,true],[false]++rep V n++rep Q 3⟩ := by
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using h5
  have h6 := finish (rep V n++rep Q 3)
  have h6' : run0 table 4 ⟨4,[true,true],[false]++rep V n++rep Q 3⟩ =
      some (sect (n+1)) := by
    have hh : Q++rep V n++rep Q 3 = rep Q (2*(n+1+1)) := by
      rw [List.append_assoc]
      change Q++(rep (Q++Q) n++rep Q 3) = _
      rw [← rep_double Q n, ← rep_add Q (2*n) 3]
      change rep Q 1 ++ rep Q (2*n+3) = _
      rw [← rep_add]
      congr 1
      omega
    have hr : [false]++rep Q (2*(n+1+1)) = rep P (2*(n+1+1))++[false] :=
      rotate false [true] (2*(n+1+1))
    have h6out : [false]++(Q++(rep V n++rep Q 3)) = (sect (n+1)).r := by
      rw [← List.append_assoc Q (rep V n) (rep Q 3),hh,hr]
      rfl
    simp only [List.append_assoc] at h6
    rw [h6out] at h6
    exact h6
  have h := join0 (join0 (join0 (join0 (join0 h1 h2') h3) h4') h5') h6'
  rw [show 2+4*n+11+6+6*n+4=10*(n+1)+13 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 13 (fun n => 10*(n+1)+13) first (by intro n; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43RF0M13

namespace BB6.Agent25Raw43RF0M20
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent25Raw43RD1Growth
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def U : List Bool := [true,false,false]
def T : List Bool := [true,false,true]
def sect (n : Nat) : Z0 := ⟨0,[],rep U (n+1)++[false,false]⟩
private theorem first : run0 table 13 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem enter (R : List Bool) : run0 table 3 ⟨0,[],U++R⟩ =
  some ⟨0,[false]++T,R⟩ := by rfl
private theorem right (L R : List Bool) :
  run0 table 3 ⟨0,[false]++L,[]++U++R⟩ =
  some ⟨0,[false]++T++L,[]++R⟩ := by rfl
private theorem turn (L : List Bool) :
  run0 table 13 ⟨0,[false]++L,[false,false]⟩ =
  some ⟨0,L,U++[false,false]⟩ := by rfl
private theorem left (L R : List Bool) :
  run0 table 3 ⟨0,[]++T++L,[]++R⟩ =
  some ⟨0,[]++L,[]++U++R⟩ := by rfl
theorem grow (n : Nat) :
    run0 table (6*(n+1)+13) (sect n) = some (sect (n+1)) := by
  have h1 : run0 table 3 (sect n) =
      some ⟨0,[false]++T,rep U n++[false,false]⟩ := by
    simpa only [sect,rep,List.append_assoc] using enter (rep U n++[false,false])
  have h2 := sweepR table 0 [false] [] U T 3 right n T [false,false]
  have h2' : run0 table (3*n) ⟨0,[false]++T,rep U n++[false,false]⟩ =
      some ⟨0,[false]++rep T (n+1),[false,false]⟩ := by
    simp only [List.append_assoc,List.nil_append] at h2
    rw [rep_snoc T n] at h2
    exact h2
  have h3 := turn (rep T (n+1))
  have h4 := sweepL table 0 [] [] T U 3 left (n+1) [] (U++[false,false])
  have h4' : run0 table (3*(n+1)) ⟨0,rep T (n+1),U++[false,false]⟩ =
      some (sect (n+1)) := by
    simp only [List.nil_append,List.append_nil] at h4
    rw [← List.append_assoc,rep_snoc U (n+1)] at h4
    exact h4
  have h := join0 (join0 (join0 h1 h2') h3) h4'
  rw [show 3+3*n+13+3*(n+1)=6*(n+1)+13 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 13 (fun n => 6*(n+1)+13) first (by intro n; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43RF0M20

namespace BB6.Agent25Raw43RF0M73
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent25Raw43RD1Growth
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def Q : List Bool := [true,false]
def U : List Bool := [true,true,false]
def O : List Bool := [true]
def sect (n : Nat) : Z0 := ⟨0,[false]++rep O (n+1),rep Q (n+2)++[true]⟩
private theorem first : run0 table 17 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem enter (L R : List Bool) :
  run0 table 7 ⟨0,[false]++L,Q++Q++R⟩ =
  some ⟨0,[false,false,false,true]++L,[true]++R⟩ := by rfl
private theorem right (L R : List Bool) :
  run0 table 4 ⟨0,[false,false]++L,[true]++Q++R⟩ =
  some ⟨0,[false,false]++Q++L,[true]++R⟩ := by rfl
private theorem turn1 (L : List Bool) :
  run0 table 4 ⟨0,[false,false]++L,[true,true]⟩ =
  some ⟨0,[false,false]++Q++L,[true]⟩ := by rfl
private theorem turn2 (L : List Bool) :
  run0 table 4 ⟨0,[false,false]++L,[true]⟩ =
  some ⟨0,Q++Q++L,[true]⟩ := by rfl
private theorem left (L R : List Bool) :
  run0 table 2 ⟨0,[]++Q++L,[]++R⟩ =
  some ⟨0,[]++L,[]++Q++R⟩ := by rfl
theorem grow (n : Nat) :
    run0 table (6*n+21) (sect n) = some (sect (n+1)) := by
  have h1 : run0 table 7 (sect n) =
      some ⟨0,[false,false]++([false]++rep O (n+2)),[true]++rep Q n++[true]⟩ := by
    simpa only [sect,rep,O,List.append_assoc,List.cons_append,List.nil_append] using enter (rep O (n+1)) (rep Q n++[true])
  have h2 := sweepR table 0 [false,false] [true] Q Q 4 right n ([false]++rep O (n+2)) [true]
  have h2' : run0 table (4*n) ⟨0,[false,false]++([false]++rep O (n+2)),[true]++rep Q n++[true]⟩ =
      some ⟨0,[false,false]++rep Q n++([false]++rep O (n+2)),[true,true]⟩ := by
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using h2
  have h3 := turn1 (rep Q n++([false]++rep O (n+2)))
  have h4 := turn2 (Q++rep Q n++([false]++rep O (n+2)))
  have h34 : run0 table 8 ⟨0,[false,false]++rep Q n++([false]++rep O (n+2)),[true,true]⟩ =
      some ⟨0,rep Q (n+3)++([false]++rep O (n+2)),[true]⟩ := by
    have h := join0 h3 h4
    simpa only [rep,List.append_assoc] using h
  have h5 := sweepL table 0 [] [] Q Q 2 left (n+3) ([false]++rep O (n+2)) [true]
  have h5' : run0 table (2*(n+3)) ⟨0,rep Q (n+3)++([false]++rep O (n+2)),[true]⟩ =
      some (sect (n+1)) := by
    simpa only [sect,List.nil_append] using h5
  have h := join0 (join0 (join0 h1 h2') h34) h5'
  rw [show 7+4*n+8+2*(n+3)=6*n+21 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 17 (fun n => 6*n+21) first (by intro n; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43RF0M73

namespace BB6.Agent25Raw43RF0M103
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent25Raw43RD1Growth
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def O : List Bool := [true]
def M : List Bool := [true,true,true]
def sect (n : Nat) : Z0 := ⟨0,[],rep O (4*n+6)⟩
private theorem first : run0 table 18 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem enter (R : List Bool) :
  run0 table 9 ⟨0,[],M++O++R⟩ =
  some ⟨0,[false]++O,M++R⟩ := by rfl
private theorem right (L R : List Bool) :
  run0 table 9 ⟨0,[false]++L,M++O++R⟩ =
  some ⟨0,[false]++O++L,M++R⟩ := by rfl
private theorem turn (L : List Bool) :
  run0 table 20 ⟨0,[false]++L,M⟩ =
  some ⟨0,M++L,[true,true,true,true]⟩ := by rfl
private theorem left (L R : List Bool) :
  run0 table 1 ⟨0,[]++O++L,[]++R⟩ =
  some ⟨0,[]++L,[]++O++R⟩ := by rfl
theorem grow (n : Nat) :
    run0 table (40*n+53) (sect n) = some (sect (n+1)) := by
  let j := 4*n+2
  have he : rep O (4*n+6) = M++O++rep O j := by
    rw [show 4*n+6=j+4 by rfl,show j+4=4+j by omega,rep_add O 4 j] <;> rfl
  have h1 : run0 table 9 (sect n) = some ⟨0,[false]++O,M++rep O j⟩ := by
    rw [sect,he]
    exact enter (rep O j)
  have h2 := sweepR table 0 [false] M O O 9 right j O []
  have h2' : run0 table (9*j) ⟨0,[false]++O,M++rep O j⟩ =
      some ⟨0,[false]++rep O (j+1),M⟩ := by
    simp only [List.append_assoc,List.append_nil] at h2
    rw [rep_snoc O j] at h2
    exact h2
  have h3 := turn (rep O (j+1))
  have he3 : M++rep O (j+1) = rep O (j+4) := by
    rw [show j+4=3+(j+1) by omega,rep_add O 3 (j+1)] <;> rfl
  rw [he3] at h3
  have h4 := sweepL table 0 [] [] O O 1 left (j+4) [] [true,true,true,true]
  have h4' : run0 table (j+4) ⟨0,rep O (j+4),[true,true,true,true]⟩ =
      some (sect (n+1)) := by
    have he4 : rep O (j+4)++[true,true,true,true] = rep O (4*(n+1)+6) := by
      change rep O (j+4)++rep O 4 = _
      rw [← rep_add,show j+4+4=4*(n+1)+6 by dsimp [j]; omega]
    simpa only [sect,Nat.one_mul,List.nil_append,List.append_nil,he4] using h4
  have h := join0 (join0 (join0 h1 h2') h3) h4'
  rw [show 9+9*j+20+(j+4)=40*n+53 by dsimp [j]; omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 18 (fun n => 40*n+53) first (by intro n; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43RF0M103

namespace BB6.Agent25Raw43RF0M119
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent25Raw43RD1Growth
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def W : List Bool := [false,false,false,false,true,true,true,true]
def U : List Bool := [false,true,true,false,false,false,true,true]
def L0 : List Bool := [false,false,false,true,true,false,false,false,true,true]
def L1 : List Bool := [true,true,false,false,false,true,true]
def sect (n : Nat) : Z0 := ⟨0,[],rep W (n+1)⟩
private theorem first : run0 table 31 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem enterLast : run0 table 30 ⟨0,[],W⟩ =
  some ⟨0,L0,[false]⟩ := by rfl
private theorem enter (R : List Bool) :
  run0 table 30 ⟨0,[],W++[false]++R⟩ =
  some ⟨0,L0,[false]++R⟩ := by rfl
private theorem rightLast (L : List Bool) :
  run0 table 30 ⟨0,L0++L,W⟩ =
  some ⟨0,L0++U++L,[false]⟩ := by rfl
private theorem right (L R : List Bool) :
  run0 table 30 ⟨0,L0++L,W++[false]++R⟩ =
  some ⟨0,L0++U++L,[false]++R⟩ := by rfl
private theorem turn (L : List Bool) :
  run0 table 31 ⟨0,L0++L,[false]⟩ =
  some ⟨0,L1++L,W⟩ := by rfl
private theorem left (L R : List Bool) :
  run0 table 12 ⟨0,L1++U++L,[]++R⟩ =
  some ⟨0,L1++L,[]++W++R⟩ := by rfl
private theorem finish (R : List Bool) :
  run0 table 12 ⟨0,L1,R⟩ =
  some ⟨0,[],W++R⟩ := by rfl
private theorem rightAll (n : Nat) (L : List Bool) :
    run0 table (30*(n+1)) ⟨0,L0++L,rep W (n+1)⟩ =
      some ⟨0,L0++rep U (n+1)++L,[false]⟩ := by
  induction n generalizing L with
  | zero => simpa only [rep,List.append_nil] using rightLast L
  | succ n ih =>
    have h1 : run0 table 30 ⟨0,L0++L,rep W (n+1+1)⟩ =
        some ⟨0,L0++U++L,rep W (n+1)⟩ := by
      simpa only [rep,W,List.append_assoc,List.cons_append,List.nil_append] using right L ([false,false,false,true,true,true,true]++rep W n)
    have h2 := ih (U++L)
    have h := join0 h1 (by simpa only [List.append_assoc] using h2)
    rw [show 30+30*(n+1)=30*(n+1+1) by omega] at h
    have hh : rep U (n+1)++(U++L) = rep U (n+1+1)++L := by
      rw [← List.append_assoc,rep_snoc U (n+1)]
      rfl
    simpa only [List.append_assoc,hh] using h
private theorem rightStart (n : Nat) :
    run0 table (30*(n+1)) (sect n) =
      some ⟨0,L0++rep U n,[false]⟩ := by
  cases n with
  | zero => simpa only [sect,rep,List.append_nil] using enterLast
  | succ n =>
    have h1 : run0 table 30 (sect (n+1)) =
        some ⟨0,L0,rep W (n+1)⟩ := by
      simpa only [sect,rep,W,List.append_assoc,List.cons_append,List.nil_append] using enter ([false,false,false,true,true,true,true]++rep W n)
    have h2 := rightAll n []
    have h := join0 h1 (by simpa only [List.append_nil] using h2)
    rw [show 30+30*(n+1)=30*(n+1+1) by omega] at h
    simpa only [List.append_nil] using h
theorem grow (n : Nat) :
    run0 table (42*n+73) (sect n) = some (sect (n+1)) := by
  have h1 := rightStart n
  have h2 := turn (rep U n)
  have h3 := sweepL table 0 L1 [] U W 12 left n [] W
  have h3' : run0 table (12*n) ⟨0,L1++rep U n,W⟩ =
      some ⟨0,L1,rep W (n+1)⟩ := by
    simp only [List.nil_append,List.append_nil] at h3
    rw [rep_snoc W n] at h3
    exact h3
  have h4 := finish (rep W (n+1))
  have h4' : run0 table 12 ⟨0,L1,rep W (n+1)⟩ = some (sect (n+1)) := by
    simpa only [sect,rep] using h4
  have h := join0 (join0 (join0 h1 h2) h3') h4'
  rw [show 30*(n+1)+31+12*n+12=42*n+73 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 31 (fun n => 42*n+73) first (by intro n; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43RF0M119

