import Raw43RD1Growth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LAA1LEM122
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent25Raw43RD1Growth (rep_add)

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def P : List Bool := [false,true]
def Q : List Bool := [true,true]
def A (m : Nat) : Z0 := ⟨0,[],rep P m⟩
def T (k : Nat) : Z0 := ⟨0,[],rep P (k+2)++Q⟩
def U (k : Nat) : Z0 := ⟨4,[],[true]++rep P (k+2)++Q⟩

private theorem enterC (R : List Bool) :
    run0 table 2 ⟨0,[],P++R⟩ = some ⟨2,[true]++Q,R⟩ := by rfl
private theorem cPush (L R : List Bool) :
    run0 table 2 ⟨2,[true]++L,[]++P++R⟩ =
      some ⟨2,[true]++Q++L,[]++R⟩ := by rfl
private theorem turn1 (L : List Bool) :
    run0 table 9 ⟨2,[true]++L,[]⟩ = some ⟨0,Q++L,Q⟩ := by rfl
private theorem turn2 (L : List Bool) :
    run0 table 2 ⟨2,[true]++L,Q⟩ = some ⟨0,[true]++L,Q⟩ := by rfl
private theorem pop (L R : List Bool) :
    run0 table 2 ⟨0,[]++Q++L,[]++R⟩ = some ⟨0,[]++L,[]++P++R⟩ := by rfl
private theorem exitE (R : List Bool) :
    run0 table 1 ⟨0,[true],R⟩ = some ⟨4,[],[true]++R⟩ := by rfl
private theorem enterF (R : List Bool) :
    run0 table 1 ⟨4,[],[true]++R⟩ = some ⟨5,Q,R⟩ := by rfl
private theorem fPush (L R : List Bool) :
    run0 table 2 ⟨5,Q++L,[]++P++R⟩ =
      some ⟨5,Q++Q++L,[]++R⟩ := by rfl
private theorem turn3 (L : List Bool) :
    run0 table 2 ⟨5,Q++L,Q⟩ = some ⟨0,Q++L,P⟩ := by rfl

private theorem qjoin (k : Nat) : Q++(rep Q k++Q)=rep Q (k+2) := by
  change rep Q 1 ++ (rep Q k ++ rep Q 1) = _
  rw [← rep_add Q k 1,← rep_add Q 1 (k+1),show 1+(k+1)=k+2 by omega]

private theorem phase1 (k : Nat) : run0 table (4*k+15) (A (k+1)) = some (T k) := by
  have h1 : run0 table 2 (A (k+1)) = some ⟨2,[true]++Q,rep P k⟩ := by
    exact enterC (rep P k)
  have h2 : run0 table (2*k) ⟨2,[true]++Q,rep P k⟩ =
      some ⟨2,[true]++rep Q k++Q,[]⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using
      sweepR table 2 [true] [] P Q 2 cPush k Q []
  have h3 : run0 table 9 ⟨2,[true]++rep Q k++Q,[]⟩ =
      some ⟨0,rep Q (k+2),Q⟩ := by
    simpa only [List.append_assoc,qjoin] using turn1 (rep Q k++Q)
  have h4 : run0 table (2*(k+2)) ⟨0,rep Q (k+2),Q⟩ = some (T k) := by
    simpa only [List.nil_append,List.append_nil,T] using
      sweepL table 0 [] [] Q P 2 pop (k+2) [] Q
  have h := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 2+2*k+9+2*(k+2)=4*k+15 by omega] at h
  exact h

private theorem phase2 (k : Nat) : run0 table (4*k+11) (T k) = some (U k) := by
  have h1 : run0 table 2 (T k) = some ⟨2,[true]++Q,rep P (k+1)++Q⟩ := by
    simpa only [T,rep,List.append_assoc] using enterC (rep P (k+1)++Q)
  have h2 : run0 table (2*(k+1)) ⟨2,[true]++Q,rep P (k+1)++Q⟩ =
      some ⟨2,[true]++rep Q (k+1)++Q,Q⟩ := by
    simpa only [List.nil_append,List.append_assoc] using
      sweepR table 2 [true] [] P Q 2 cPush (k+1) Q Q
  have hL : [true]++(rep Q (k+1)++Q) = rep Q (k+2)++[true] := by
    change [true]++(rep Q (k+1)++rep Q 1)=_
    rw [← rep_add Q (k+1) 1]
    exact rotate true [true] (k+2)
  have h3 : run0 table 2 ⟨2,[true]++rep Q (k+1)++Q,Q⟩ =
      some ⟨0,rep Q (k+2)++[true],Q⟩ := by
    simpa only [List.append_assoc,hL] using turn2 (rep Q (k+1)++Q)
  have h4 : run0 table (2*(k+2)) ⟨0,rep Q (k+2)++[true],Q⟩ =
      some ⟨0,[true],rep P (k+2)++Q⟩ := by
    simpa only [List.nil_append] using
      sweepL table 0 [] [] Q P 2 pop (k+2) [true] Q
  have h5 : run0 table 1 ⟨0,[true],rep P (k+2)++Q⟩ = some (U k) :=
    exitE (rep P (k+2)++Q)
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 2+2*(k+1)+2+2*(k+2)+1=4*k+11 by omega] at h
  exact h

private theorem phase3 (k : Nat) : run0 table (4*k+13) (U k) = some (A (k+4)) := by
  have h1 : run0 table 1 (U k) = some ⟨5,Q,rep P (k+2)++Q⟩ :=
    enterF (rep P (k+2)++Q)
  have h2 : run0 table (2*(k+2)) ⟨5,Q,rep P (k+2)++Q⟩ =
      some ⟨5,Q++rep Q (k+2),Q⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using
      sweepR table 5 Q [] P Q 2 fPush (k+2) [] Q
  have h3 : run0 table 2 ⟨5,Q++rep Q (k+2),Q⟩ =
      some ⟨0,rep Q (k+3),P⟩ := turn3 (rep Q (k+2))
  have hR : rep P (k+3)++P = rep P (k+4) := by
    change rep P (k+3)++rep P 1=_
    rw [← rep_add P (k+3) 1]
  have h4 : run0 table (2*(k+3)) ⟨0,rep Q (k+3),P⟩ = some (A (k+4)) := by
    simpa only [List.nil_append,List.append_nil,hR,A] using
      sweepL table 0 [] [] Q P 2 pop (k+3) [] P
  have h := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 1+2*(k+2)+2+2*(k+3)=4*k+13 by omega] at h
  exact h

def S (n : Nat) : Z0 := A (3*n+3)
private theorem first : run0 table 27 ⟨0,[],[]⟩ = some (S 0) := by rfl

theorem growth (n : Nat) : run0 table (36*n+63) (S n) = some (S (n+1)) := by
  have h := join0 (join0 (phase1 (3*n+2)) (phase2 (3*n+2))) (phase3 (3*n+2))
  rw [show 4*(3*n+2)+15+(4*(3*n+2)+11)+(4*(3*n+2)+13)=36*n+63 by omega,
    show 3*n+2+1=3*n+3 by omega,show 3*n+2+4=3*(n+1)+3 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table S 27 (fun n => 36*n+63) first (by intro n; omega) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent25Raw43B1LAA1LEM122
