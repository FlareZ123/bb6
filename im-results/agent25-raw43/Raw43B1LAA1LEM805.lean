import Raw43RD1Growth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LAA1LEM805
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent25Raw43RD1Growth (rep_add)

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def P : List Bool := [true,true]
def Q : List Bool := [true,true,true]
def S (n : Nat) : Z0 := ⟨1,[],rep P (3*n+2)⟩

private theorem pair_triples (n : Nat) : rep P (3*n) = rep Q (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,show 2*(n+1)=2+2*n by omega,
      rep_add P 3 (3*n),rep_add Q 2 (2*n),ih]
    rfl

private theorem first : run0 table 11 ⟨0,[],[]⟩ = some (S 0) := by rfl
private theorem enter (R : List Bool) :
    run0 table 4 ⟨1,[],P++P++R⟩ = some ⟨1,[false]++P,P++R⟩ := by rfl
private theorem push (L R : List Bool) :
    run0 table 4 ⟨1,[false]++L,P++P++R⟩ = some ⟨1,[false]++P++L,P++R⟩ := by rfl
private theorem turn (L : List Bool) :
    run0 table 17 ⟨1,[false]++L,P⟩ = some ⟨1,rep P 2++L,rep P 2⟩ := by rfl
private theorem pop (L R : List Bool) :
    run0 table 3 ⟨1,[]++Q++L,[]++R⟩ = some ⟨1,[]++L,[]++Q++R⟩ := by rfl

theorem growth (n : Nat) : run0 table (18*n+27) (S n) = some (S (n+1)) := by
  have h1 : run0 table 4 (S n) = some ⟨1,[false]++P,P++rep P (3*n)⟩ := by
    unfold S
    rw [show 3*n+2=2+3*n by omega,rep_add P 2 (3*n)]
    exact enter (rep P (3*n))
  have h2 : run0 table (4*(3*n)) ⟨1,[false]++P,P++rep P (3*n)⟩ =
      some ⟨1,[false]++rep P (3*n)++P,P⟩ := by
    simpa only [List.append_nil,List.append_assoc] using
      sweepR table 1 [false] P P P 4 push (3*n) P []
  have hL : rep P 2 ++ (rep P (3*n) ++ P) = rep Q (2*(n+1)) := by
    change rep P 2 ++ (rep P (3*n) ++ rep P 1) = _
    rw [← rep_add P (3*n) 1,← rep_add P 2 (3*n+1),
      show 2+(3*n+1)=3*(n+1) by omega,pair_triples]
  have h3 : run0 table 17 ⟨1,[false]++rep P (3*n)++P,P⟩ =
      some ⟨1,rep Q (2*(n+1)),rep P 2⟩ := by
    simpa only [List.append_assoc,hL] using turn (rep P (3*n)++P)
  have hR : rep Q (2*(n+1)) ++ rep P 2 = rep P (3*(n+1)+2) := by
    rw [← pair_triples (n+1),← rep_add]
  have h4 : run0 table (3*(2*(n+1))) ⟨1,rep Q (2*(n+1)),rep P 2⟩ =
      some (S (n+1)) := by
    simpa only [List.nil_append,List.append_nil,hR,S] using
      sweepL table 1 [] [] Q Q 3 pop (2*(n+1)) [] (rep P 2)
  have h := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 4+4*(3*n)+17+3*(2*(n+1))=18*n+27 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table S 11 (fun n => 18*n+27) first (by intro n; omega) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent25Raw43B1LAA1LEM805
