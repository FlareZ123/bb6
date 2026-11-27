import Raw43RD1Growth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43RC0M43
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent25Raw43RD1Growth
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none

def U : List Bool := [false,false,true]
def V : List Bool := [false,true,true,true]
def d1 : List Bool := [true,false,true]
def d2 : List Bool := [false,false,false]
def d3 : List Bool := [true,false,false]
def sect (n : Nat) : Z0 := ⟨0,[],rep U (n+1)++V⟩
def R (n : Nat) : List Bool := rep U n++V

private theorem start : run0 table 28 ⟨0,[],[]⟩ = some (sect 0) := by rfl
private theorem start0 (L T : List Bool) :
  run0 table 3 ⟨0,[false]++L,U++T⟩ =
  some ⟨3,d1++[true]++L,T⟩ := by rfl
private theorem startBlank (T : List Bool) :
  run0 table 3 ⟨0,[],U++T⟩ =
  some ⟨3,d1++[true],T⟩ := by rfl
private theorem short0 (L : List Bool) :
  run0 table 6 ⟨0,[false]++L,V⟩ =
  some ⟨0,[true]++L,V⟩ := by rfl
private theorem right (L T : List Bool) :
  run0 table 3 ⟨3,d1++L,[]++U++T⟩ =
  some ⟨3,d1++U++L,[]++T⟩ := by rfl
private theorem turn (L : List Bool) :
  run0 table 6 ⟨3,d1++L,V⟩ =
  some ⟨0,U++L,V⟩ := by rfl
private theorem start1 (L T : List Bool) :
  run0 table 4 ⟨0,d1++L,[false]++T⟩ =
  some ⟨3,d3++L,[false]++T⟩ := by rfl
private theorem short1 (L : List Bool) :
  run0 table 6 ⟨3,d3++L,V⟩ =
  some ⟨0,d2++L,V⟩ := by rfl
private theorem enter1 (L T : List Bool) :
  run0 table 3 ⟨3,d3++L,U++T⟩ =
  some ⟨3,d1++d2++L,T⟩ := by rfl
private theorem pop3 (L T : List Bool) :
  run0 table 3 ⟨0,d3++L,T⟩ =
  some ⟨0,L,U++T⟩ := by rfl
private theorem final (T : List Bool) :
  run0 table 3 ⟨0,[true],T⟩ =
  some ⟨0,[],U++T⟩ := by rfl

/-- D scans any number of 001 blocks and returns to A. -/
theorem pushD (n : Nat) (L : List Bool) :
  run0 table (3*n+6) ⟨3,d1++L,R n⟩ =
  some ⟨0,rep U (n+1)++L,V⟩ := by
  have h := sweepR table 3 d1 [] U U 3 right n L V
  have h' : run0 table (3*n) ⟨3,d1++L,R n⟩ =
      some ⟨3,d1++rep U n++L,V⟩ := by
    simpa only [R,List.nil_append] using h
  have hh := join0 h' (turn (rep U n++L))
  simpa only [rep,List.append_assoc] using hh

theorem fill0 (n : Nat) (L : List Bool) :
  run0 table (3*n+6) ⟨0,[false]++L,R n⟩ =
  some ⟨0,rep U n++[true]++L,V⟩ := by
  cases n with
  | zero => simpa only [R,rep,List.nil_append] using short0 L
  | succ n =>
    have h1 : run0 table 3 ⟨0,[false]++L,R (n+1)⟩ =
        some ⟨3,d1++([true]++L),R n⟩ := by
      simpa only [R,rep,List.append_assoc] using start0 L (R n)
    have h := join0 h1 (pushD n ([true]++L))
    rw [show 3+(3*n+6)=3*(n+1)+6 by omega] at h
    simpa only [List.append_assoc] using h

theorem fill1 (n : Nat) (L : List Bool) :
  run0 table (3*n+10) ⟨0,d1++L,R n⟩ =
  some ⟨0,rep U n++d2++L,V⟩ := by
  have h1 : run0 table 4 ⟨0,d1++L,R n⟩ =
      some ⟨3,d3++L,R n⟩ := by
    cases n with
    | zero => exact start1 L [true,true,true]
    | succ n =>
      simpa only [R,rep,U,List.append_assoc,List.cons_append,List.nil_append] using start1 L ([false,true]++R n)
  cases n with
  | zero => simpa only [R,rep,List.nil_append] using join0 h1 (short1 L)
  | succ n =>
    have h2 : run0 table 3 ⟨3,d3++L,R (n+1)⟩ =
        some ⟨3,d1++(d2++L),R n⟩ := by
      simpa only [R,rep,List.append_assoc] using enter1 L (R n)
    have h := join0 (join0 h1 h2) (pushD n (d2++L))
    rw [show 4+3+(3*n+6)=3*(n+1)+10 by omega] at h
    simpa only [List.append_assoc] using h

def time : Nat → Nat
  | 0 => 0
  | n+1 => 4*time n+9*n+25

/-- Four digit phases, with an arbitrary untouched left suffix.
    The recursive calls restore the n lower digits between successive phases. -/
theorem erase (n : Nat) (L : List Bool) :
    run0 table (time n) ⟨0,rep U n++L,V⟩ = some ⟨0,L,R n⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h0 : run0 table (time n) ⟨0,rep U (n+1)++L,V⟩ =
        some ⟨0,U++L,R n⟩ := by
      have h := ih (U++L)
      rw [← List.append_assoc,rep_snoc U n] at h
      exact h
    have h1 : run0 table (3*n+6) ⟨0,U++L,R n⟩ =
        some ⟨0,rep U n++(d1++L),V⟩ := by
      simpa only [U,d1,List.append_assoc,List.cons_append,List.nil_append] using fill0 n ([false,true]++L)
    have h2 := ih (d1++L)
    have h3 : run0 table (3*n+10) ⟨0,d1++L,R n⟩ =
        some ⟨0,rep U n++(d2++L),V⟩ := by
      simpa only [List.append_assoc] using fill1 n L
    have h4 := ih (d2++L)
    have h5 : run0 table (3*n+6) ⟨0,d2++L,R n⟩ =
        some ⟨0,rep U n++(d3++L),V⟩ := by
      simpa only [d2,d3,List.append_assoc,List.cons_append,List.nil_append] using fill0 n ([false,false]++L)
    have h6 := ih (d3++L)
    have h7 : run0 table 3 ⟨0,d3++L,R n⟩ = some ⟨0,L,R (n+1)⟩ := by
      simpa only [R,rep,List.append_assoc] using pop3 L (R n)
    have h := join0 (join0 (join0 (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4) h5) h6) h7
    rw [show time n+(3*n+6)+time n+(3*n+10)+time n+(3*n+6)+time n+3=time (n+1) by simp only [time]; omega] at h
    exact h

def cost (n : Nat) := time (n+1)+3*(n+1)+9

theorem grow (n : Nat) :
    run0 table (cost n) (sect n) = some (sect (n+1)) := by
  have h0 : run0 table 3 (sect n) = some ⟨3,d1++[true],R n⟩ := by
    simpa only [sect,R,rep,List.append_assoc] using startBlank (R n)
  have h1 := pushD n [true]
  have h2 := erase (n+1) [true]
  have h3 : run0 table 3 ⟨0,[true],R (n+1)⟩ = some (sect (n+1)) := by
    simpa only [sect,R,rep,List.append_assoc] using final (R (n+1))
  have h := join0 (join0 (join0 h0 h1) h2) h3
  rw [show 3+(3*n+6)+time (n+1)+3=cost n by simp only [cost]; omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table sect 28 cost start (by intro n; unfold cost; omega) grow m hm
#print axioms never
end BB6.Agent25Raw43RC0M43
