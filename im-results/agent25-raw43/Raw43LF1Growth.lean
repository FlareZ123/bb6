import Raw43RD1Growth
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent25Raw43LF1M71
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
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def P : List Bool := [false,true]
def U := P++P
def T : List Bool := [false,false,false,true]
def sect (n : Nat) : Z0 := ⟨0,[],rep P (2*(n+1))⟩
private theorem first : run0 table 11 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem enter (R : List Bool) : run0 table 2 ⟨0,[],P++R⟩ = some ⟨2,[true,true,true],R⟩ := by rfl
private theorem right (L R : List Bool) :
  run0 table 4 ⟨2,[true,true]++L,[]++U++R⟩ =
  some ⟨2,[true,true]++T++L,[]++R⟩ := by rfl
private theorem turn (L : List Bool) :
  run0 table 15 ⟨2,[true,true]++L,P⟩ =
  some ⟨4,[true]++L,rep P 3⟩ := by rfl
private theorem left (L R : List Bool) :
  run0 table 4 ⟨4,[true]++T++L,[]++R⟩ =
  some ⟨4,[true]++L,[]++U++R⟩ := by rfl
private theorem finish (R : List Bool) :
  run0 table 2 ⟨4,[true,true],R⟩ = some ⟨0,[],P++R⟩ := by rfl
theorem grow (n : Nat) :
    run0 table (8*(n+1)+11) (sect n) = some (sect (n+1)) := by
  have he : rep P (2*(n+1)) = P++rep U n++P := by
    rw [show 2*(n+1)=1+(2*n+1) by omega,rep_add P 1 (2*n+1),rep_add P (2*n) 1,rep_double P n]
    rfl
  have h1 : run0 table 2 (sect n) =
      some ⟨2,[true,true,true],rep U n++P⟩ := by
    rw [sect,he]
    simpa only [List.append_assoc] using enter (rep U n++P)
  have h2 := sweepR table 2 [true,true] [] U T 4 right n [true] P
  have h2' : run0 table (4*n) ⟨2,[true,true,true],rep U n++P⟩ =
      some ⟨2,[true,true]++rep T n++[true],P⟩ := by
    simpa only [List.nil_append,List.cons_append,List.append_nil] using h2
  have h3 := turn (rep T n++[true])
  have h4 := sweepL table 4 [true] [] T U 4 left n [true] (rep P 3)
  have h4' : run0 table (4*n) ⟨4,[true]++rep T n++[true],rep P 3⟩ =
      some ⟨4,[true,true],rep U n++rep P 3⟩ := by
    simpa only [List.nil_append,List.cons_append,List.append_nil] using h4
  have h5 := finish (rep U n++rep P 3)
  have hh : P++(rep U n++rep P 3) = rep P (2*(n+1+1)) := by
    change P++(rep (P++P) n++rep P 3) = _
    rw [← rep_double P n,← rep_add P (2*n) 3]
    change rep P 1 ++ rep P (2*n+3) = _
    rw [← rep_add]
    congr 1
    omega
  rw [hh] at h5
  have h := join0 (join0 (join0 (join0 h1 h2') h3) h4') h5
  rw [show 2+4*n+15+4*n+2=8*(n+1)+11 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 11 (fun n => 8*(n+1)+11) first (by intro n; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43LF1M71

namespace BB6.Agent25Raw43LF1M82
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
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def P : List Bool := [false,true]
def U := P++P
def T : List Bool := [false,false,false,true]
def sect (n : Nat) : Z0 := ⟨0,[],rep P (2*(n+1))⟩
private theorem first : run0 table 13 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem enter (R : List Bool) : run0 table 2 ⟨0,[],P++R⟩ = some ⟨2,[true,true,true],R⟩ := by rfl
private theorem right (L R : List Bool) :
  run0 table 4 ⟨2,[true,true]++L,[]++U++R⟩ =
  some ⟨2,[true,true]++T++L,[]++R⟩ := by rfl
private theorem turn (L : List Bool) :
  run0 table 19 ⟨2,[true,true]++L,P⟩ =
  some ⟨4,[true]++L,rep P 3⟩ := by rfl
private theorem left (L R : List Bool) :
  run0 table 6 ⟨4,[true]++T++L,[]++R⟩ =
  some ⟨4,[true]++L,[]++U++R⟩ := by rfl
private theorem finish (R : List Bool) :
  run0 table 2 ⟨4,[true,true],R⟩ = some ⟨0,[],P++R⟩ := by rfl
theorem grow (n : Nat) :
    run0 table (10*(n+1)+13) (sect n) = some (sect (n+1)) := by
  have he : rep P (2*(n+1)) = P++rep U n++P := by
    rw [show 2*(n+1)=1+(2*n+1) by omega,rep_add P 1 (2*n+1),rep_add P (2*n) 1,rep_double P n]
    rfl
  have h1 : run0 table 2 (sect n) =
      some ⟨2,[true,true,true],rep U n++P⟩ := by
    rw [sect,he]
    simpa only [List.append_assoc] using enter (rep U n++P)
  have h2 := sweepR table 2 [true,true] [] U T 4 right n [true] P
  have h2' : run0 table (4*n) ⟨2,[true,true,true],rep U n++P⟩ =
      some ⟨2,[true,true]++rep T n++[true],P⟩ := by
    simpa only [List.nil_append,List.cons_append,List.append_nil] using h2
  have h3 := turn (rep T n++[true])
  have h4 := sweepL table 4 [true] [] T U 6 left n [true] (rep P 3)
  have h4' : run0 table (6*n) ⟨4,[true]++rep T n++[true],rep P 3⟩ =
      some ⟨4,[true,true],rep U n++rep P 3⟩ := by
    simpa only [List.nil_append,List.cons_append,List.append_nil] using h4
  have h5 := finish (rep U n++rep P 3)
  have hh : P++(rep U n++rep P 3) = rep P (2*(n+1+1)) := by
    change P++(rep (P++P) n++rep P 3) = _
    rw [← rep_double P n,← rep_add P (2*n) 3]
    change rep P 1 ++ rep P (2*n+3) = _
    rw [← rep_add]
    congr 1
    omega
  rw [hh] at h5
  have h := join0 (join0 (join0 (join0 h1 h2') h3) h4') h5
  rw [show 2+4*n+19+6*n+2=10*(n+1)+13 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 13 (fun n => 10*(n+1)+13) first (by intro n; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43LF1M82
