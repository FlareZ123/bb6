import Raw43RD1Growth
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent25Raw43RE1M10
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent25Raw43RD1Growth
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def U : List Bool := [true,true,false,true,true,false]
def T : List Bool := [false,false,true]
def V : List Bool := [false,true,true]
def W := T++T
def sect (n : Nat) : Z0 := ⟨0,[],[false]++rep U (n+1)⟩

private theorem start : run0 table 15 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem first (R : List Bool) :
    run0 table 12 ⟨0,[],[false]++U++R⟩ =
    some ⟨0,[false]++W,[false]++R⟩ := by rfl
private theorem right (L R : List Bool) :
    run0 table 12 ⟨0,[false]++L,[false]++U++R⟩ =
    some ⟨0,[false]++W++L,[false]++R⟩ := by rfl
private theorem turn (L : List Bool) :
    run0 table 9 ⟨0,[false]++L,[false]⟩ =
    some ⟨0,[true]++T++L,[false]⟩ := by rfl
private theorem left (L R : List Bool) :
    run0 table 3 ⟨0,[true]++T++L,[]++R⟩ =
    some ⟨0,[true]++L,[]++V++R⟩ := by rfl
private theorem finish (R : List Bool) :
    run0 table 3 ⟨0,[true],R⟩ =
    some ⟨0,[],V++R⟩ := by rfl

theorem grow (n : Nat) :
    run0 table (18*(n+1)+15) (sect n) = some (sect (n+1)) := by
  have h1 : run0 table 12 (sect n) =
      some ⟨0,[false]++W,[false]++rep U n⟩ := by
    simpa only [sect,rep,List.append_assoc] using first (rep U n)
  have h2 := sweepR table 0 [false] [false] U W 12 right n W []
  have h2' : run0 table (12*n) ⟨0,[false]++W,[false]++rep U n⟩ =
      some ⟨0,[false]++rep W (n+1),[false]⟩ := by
    simpa only [List.append_nil,rep_snoc,rep] using h2
  have h3 := turn (rep W (n+1))
  have h3' : run0 table 9 ⟨0,[false]++rep W (n+1),[false]⟩ =
      some ⟨0,[true]++rep T (2*(n+1)+1),[false]⟩ := by
    rw [show rep T (2*(n+1)+1)=T++rep T (2*(n+1)) from rfl,rep_double T (n+1)]
    simpa only [W,List.append_assoc] using h3
  have h4 := sweepL table 0 [true] [] T V 3 left (2*(n+1)+1) [] [false]
  have h4' : run0 table (3*(2*(n+1)+1)) ⟨0,[true]++rep T (2*(n+1)+1),[false]⟩ =
      some ⟨0,[true],rep V (2*(n+1)+1)++[false]⟩ := by
    simpa only [List.append_nil,List.nil_append] using h4
  have h5 := finish (rep V (2*(n+1)+1)++[false])
  have h5' : run0 table 3 ⟨0,[true],rep V (2*(n+1)+1)++[false]⟩ =
      some (sect (n+1)) := by
    have he : V++rep V (2*(n+1)+1) = rep V (2*(n+2)) := by
      rw [show 2*(n+2)=(2*(n+1)+1)+1 by omega,rep]
    have hr : rep V (2*(n+2))++[false] = [false]++rep U (n+2) := by
      rw [rep_double V (n+2)]
      exact (rotate false [true,true,false,true,true] (n+2)).symm
    simpa only [sect,← List.append_assoc,he,hr,Nat.add_assoc] using h5
  have h := join0 (join0 (join0 (join0 h1 h2') h3') h4') h5'
  rw [show 12+12*n+9+3*(2*(n+1)+1)+3=18*(n+1)+15 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 15 (fun n => 18*(n+1)+15) start (by intro n; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43RE1M10

namespace BB6.Agent25Raw43RE1M55
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
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def Z : List Bool := [false,false]
def O : List Bool := [true,true]
def tail (n : Nat) : List Bool := [true,false]++rep [true] n++[false,true]
def sect (n : Nat) : Z0 := ⟨0,[],[true]++rep [false] (2*(n+1))++tail n⟩

private theorem start : run0 table 15 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem first (R : List Bool) :
    run0 table 3 ⟨0,[],[true,false]++R⟩ =
    some ⟨0,[false,true],[true]++R⟩ := by rfl
private theorem right (L R : List Bool) :
    run0 table 3 ⟨0,[false]++L,[true]++[false]++R⟩ =
    some ⟨0,[false]++[true]++L,[true]++R⟩ := by rfl
private theorem turn1 (L R : List Bool) :
    run0 table 4 ⟨0,[false]++L,[true,true,false]++R⟩ =
    some ⟨0,[true,false,true]++L,[true]++R⟩ := by rfl
private theorem turn2 (L R : List Bool) :
    run0 table 4 ⟨0,[true,false,true]++L,[true]++R⟩ =
    some ⟨0,[true]++L,[true,false,true]++R⟩ := by rfl
private theorem left (L R : List Bool) :
    run0 table 2 ⟨0,[true]++O++L,[]++R⟩ =
    some ⟨0,[true]++L,[]++Z++R⟩ := by rfl
private theorem finish (R : List Bool) :
    run0 table 3 ⟨0,[true],R⟩ =
    some ⟨0,[],[true,false,false]++R⟩ := by rfl

theorem grow (n : Nat) :
    run0 table (8*(n+1)+11) (sect n) = some (sect (n+1)) := by
  let j := 2*n+1
  have hj : 2*(n+1)=j+1 := by dsimp [j]; omega
  have h1 : run0 table 3 (sect n) =
      some ⟨0,[false,true],[true]++rep [false] j++tail n⟩ := by
    rw [sect,hj]
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using first (rep [false] j++tail n)
  have h2 := sweepR table 0 [false] [true] [false] [true] 3 right j [true] (tail n)
  have h2' : run0 table (3*j) ⟨0,[false,true],[true]++rep [false] j++tail n⟩ =
      some ⟨0,[false]++rep [true] (j+1),[true]++tail n⟩ := by
    simpa only [List.cons_append,List.nil_append,rep_snoc,rep] using h2
  have h3 := turn1 (rep [true] (j+1)) (rep [true] n++[false,true])
  have h4 := turn2 (rep [true] (j+1)) (rep [true] n++[false,true])
  have h34 : run0 table 8 ⟨0,[false]++rep [true] (j+1),[true]++tail n⟩ =
      some ⟨0,[true]++rep O (n+1),tail (n+1)⟩ := by
    have h := join0 h3 h4
    rw [← hj,rep_double [true] (n+1)] at h
    simpa only [tail,O,rep,List.append_assoc,List.cons_append,List.nil_append] using h
  have h5 := sweepL table 0 [true] [] O Z 2 left (n+1) [] (tail (n+1))
  have h5' : run0 table (2*(n+1)) ⟨0,[true]++rep O (n+1),tail (n+1)⟩ =
      some ⟨0,[true],rep Z (n+1)++tail (n+1)⟩ := by
    simpa only [List.append_nil,List.nil_append] using h5
  have h6 : run0 table 3 ⟨0,[true],rep Z (n+1)++tail (n+1)⟩ =
      some (sect (n+1)) := by
    have h := finish (rep Z (n+1)++tail (n+1))
    rw [sect,rep_double [false] (n+1+1)]
    change run0 table 3 _ = some ⟨0,[],[true]++rep Z (n+1+1)++tail (n+1)⟩
    simpa only [rep,Z,List.append_assoc,List.cons_append,List.nil_append] using h
  have h := join0 (join0 (join0 (join0 h1 h2') h34) h5') h6
  rw [show 3+3*j+8+2*(n+1)+3=8*(n+1)+11 by dsimp [j]; omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 15 (fun n => 8*(n+1)+11) start (by intro n; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43RE1M55
