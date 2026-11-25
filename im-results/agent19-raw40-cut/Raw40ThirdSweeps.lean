import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.LC1RD
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1LC_1RC1RD_0RD0RE_1LD1LA_1RC0LF_1LE---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def P : List Bool := [false,true]
def family (n : Nat) : Z0 := ⟨0,rep P (3*n+4),[true,true,true]⟩
theorem entry : run0 table 39 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem start (L : List Bool) :
    run0 table 6 ⟨0,P++L,[true,true,true]⟩ = some ⟨5,P++L,[false,true,true]⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 2 ⟨5,P++L,R⟩ = some ⟨5,L,P++R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 2 ⟨2,[true,true]++L,P++R⟩ = some ⟨2,[true,true]++P++L,R⟩ := by rfl

theorem leftTurn (R : List Bool) :
    run0 table 2 ⟨5,[],R⟩ = some ⟨2,[true,true],R⟩ := by rfl

theorem rightTurn (L : List Bool) :
    run0 table 2 ⟨2,[true,true]++L,[true]⟩ = some ⟨5,P++L,[false]⟩ := by rfl

theorem finish (L : List Bool) :
    run0 table 6 ⟨2,[true,true]++L,[false]⟩ = some ⟨0,P++L,[true,true,true]⟩ := by rfl

theorem leftSweep (k : Nat) (R : List Bool) :
    run0 table (2*k) ⟨5,rep P k,R⟩ = some ⟨5,[],rep P k++R⟩ := by
  simpa using sweepL table 5 [] [] P P 2 leftOne k [] R

theorem rightSweep (k : Nat) (R : List Bool) :
    run0 table (2*k) ⟨2,[true,true],rep P k++R⟩ = some ⟨2,[true,true]++rep P k,R⟩ := by
  simpa using sweepR table 2 [true,true] [] P P 2 rightOne k [] R

theorem epoch (k : Nat) : run0 table (8*(k+1)+28) ⟨0,rep P (k+1),[true,true,true]⟩ =
    some ⟨0,rep P (k+4),[true,true,true]⟩ := by
  have h1 := start (rep P k)
  have h1' : run0 table 6 ⟨0,rep P (k+1),[true,true,true]⟩ = some ⟨5,rep P (k+1),[false,true,true]⟩ := h1
  have h2 := leftSweep (k+1) [false,true,true]
  have h3 := leftTurn (rep P (k+1)++[false,true,true])
  have h3' : run0 table 2 ⟨5,[],rep P (k+1)++[false,true,true]⟩ = some ⟨2,[true,true],rep P (k+2)++[true]⟩ := by
    have eq : rep P (k+1)++[false,true,true] = rep P (k+2)++[true] := by
      change rep P (k+1)++(P++[true]) = rep P (k+2)++[true]
      rw [← List.append_assoc,rep_snoc]; rfl
    rw [← eq]; exact h3
  have h4 := rightSweep (k+2) [true]
  have h5 : run0 table 2 ⟨2,[true,true]++rep P (k+2),[true]⟩ = some ⟨5,rep P (k+3),[false]⟩ := rightTurn (rep P (k+2))
  have h6 := leftSweep (k+3) [false]
  have h7 := leftTurn (rep P (k+3)++[false])
  have h8 := rightSweep (k+3) [false]
  have h9 : run0 table 6 ⟨2,[true,true]++rep P (k+3),[false]⟩ = some ⟨0,rep P (k+4),[true,true,true]⟩ := finish (rep P (k+3))
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h1' h2) h3') h4) h5) h6) h7) h8) h9
  rw [show 6+2*(k+1)+2+2*(k+2)+2+2*(k+3)+2+2*(k+3)+6=8*(k+1)+28 by omega] at H
  exact H

theorem growth (n : Nat) : run0 table (24*n+60) (family n) = some (family (n+1)) := by
  have H := epoch (3*n+3)
  rw [show 8*(3*n+3+1)+28=24*n+60 by omega] at H
  simpa only [family,show 3*n+3+1=3*n+4 by omega,show 3*n+3+4=3*(n+1)+4 by omega] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 39 (fun n => 24*n+60) entry (by omega) growth m hm
#print axioms never
end BB6.Agent19Raw40.LC1RD

namespace BB6.Agent19Raw40.LC1RDAlt
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1LC_1RC1RD_0RD1LE_1LD1LA_0LA1RF_---0RE
-- F0 is unqueried on the two-family invariant.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def P : List Bool := [false,true]
def U : List Bool := [true]
def Q : List Bool := P++P
def W : List Bool := [true,true,true,true]
private theorem rep_add (p : List Bool) (n m : Nat) : rep p (n+m) = rep p n ++ rep p m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=(n+m)+1 by omega,rep,ih]; simp only [rep,List.append_assoc]
private theorem rep_mul (p : List Bool) (n m : Nat) : rep (rep p n) m = rep p (m*n) := by
  induction m with
  | zero => simp [rep]
  | succ m ih => rw [rep,ih,Nat.succ_mul,Nat.add_comm (m*n) n,rep_add]

def extra (m : Nat) : Z0 := ⟨0,rep P (2*m+3)++[true],[false]⟩
def pure (m : Nat) : Z0 := ⟨0,rep P (2*m+3),[false]⟩

theorem start (L : List Bool) :
  run0 table 12 ⟨0,P++P++P++L,[false]⟩ = some ⟨0,P++L,[true,false,true,true,true,true,true]⟩ := by rfl

theorem leftOne (L R : List Bool) :
  run0 table 10 ⟨0,P++Q++L,[true,false,true]++R⟩ = some ⟨0,P++L,[true,false,true]++W++R⟩ := by rfl

theorem turnExtra (R : List Bool) :
  run0 table 6 ⟨0,P++[true],[true,false,true]++R⟩ = some ⟨4,[true],rep U 5++R⟩ := by rfl

theorem turnPure (R : List Bool) :
  run0 table 7 ⟨0,P,[true,false,true]++R⟩ = some ⟨0,[],[false]++rep U 5++R⟩ := by rfl

theorem pureStart (R : List Bool) :
  run0 table 5 ⟨0,[],[false,true,true]++R⟩ = some ⟨4,[true,false,true,true],R⟩ := by rfl

theorem rightOne (L R : List Bool) :
  run0 table 2 ⟨4,[true]++L,[true]++[true,true]++R⟩ = some ⟨4,[true]++P++L,[true]++R⟩ := by rfl

theorem finish (L : List Bool) :
  run0 table 3 ⟨4,[true]++L,[true]⟩ = some ⟨0,P++L,[false]⟩ := by rfl

theorem common (m : Nat) (L : List Bool) :
  run0 table (12+10*m) ⟨0,rep P (2*m+3)++L,[false]⟩ =
    some ⟨0,P++L,[true,false,true]++rep U (4*m+4)⟩ := by
  have he : rep P (2*m+3) = P++P++P++rep Q m := by
    change rep P (2*m+3) = rep P 3++rep (rep P 2) m
    rw [rep_mul,← rep_add]; congr 1; omega
  have h1 := start (rep Q m++L)
  have h1' : run0 table 12 ⟨0,rep P (2*m+3)++L,[false]⟩ =
      some ⟨0,P++rep Q m++L,[true,false,true]++rep U 4⟩ := by
    rw [he,show [true,false,true]++rep U 4 = [true,false,true,true,true,true,true] by rfl]; simpa only [List.append_assoc] using h1
  have h2 := sweepL table 0 P [true,false,true] Q W 10 leftOne m L (rep U 4)
  have eq : rep W m++rep U 4 = rep U (4*m+4) := by
    change rep (rep U 4) m++rep U 4 = _
    rw [rep_mul,← rep_add]; congr 1; omega
  have h2' : run0 table (10*m) ⟨0,P++rep Q m++L,[true,false,true]++rep U 4⟩ =
      some ⟨0,P++L,[true,false,true]++rep U (4*m+4)⟩ := by
    simpa only [List.append_assoc,eq] using h2
  exact join0 h1' h2'

theorem rightSweep (k : Nat) (L : List Bool) :
    run0 table (2*k) ⟨4,[true]++L,rep U (2*k+1)⟩ = some ⟨4,[true]++rep P k++L,[true]⟩ := by
  have h := sweepR table 4 [true] [true] [true,true] P 2 rightOne k L []
  have eq : [true]++rep [true,true] k = rep U (2*k+1) := by
    change rep U 1++rep (rep U 2) k = _
    rw [rep_mul,← rep_add]; congr 1; omega
  simpa only [List.append_nil,eq] using h

theorem extraEpoch (m : Nat) : run0 table (14*m+29) (extra m) = some (pure (m+1)) := by
  have h1 := common m [true]
  have h2 := turnExtra (rep U (4*m+4))
  have h2' : run0 table 6 ⟨0,P++[true],[true,false,true]++rep U (4*m+4)⟩ = some ⟨4,[true],rep U (2*(2*m+4)+1)⟩ := by
    simpa only [← rep_add,show 5+(4*m+4)=2*(2*m+4)+1 by omega] using h2
  have h3 := rightSweep (2*m+4) []
  simp only [List.append_nil] at h3
  have h4 := finish (rep P (2*m+4))
  have H := join0 (join0 (join0 h1 h2') h3) h4
  rw [show 12+10*m+6+2*(2*m+4)+3=14*m+29 by omega] at H
  change run0 table (14*m+29) ⟨0,rep P (2*m+3)++[true],[false]⟩ = some ⟨0,rep P (2*(m+1)+3),[false]⟩
  rw [show 2*(m+1)+3=2*m+4+1 by omega]
  exact H

theorem pureEpoch (m : Nat) : run0 table (14*m+33) (pure m) = some (extra (m+1)) := by
  have h1 := common m []
  simp only [List.append_nil] at h1
  have h2 := turnPure (rep U (4*m+4))
  have h2' : run0 table 7 ⟨0,P,[true,false,true]++rep U (4*m+4)⟩ = some ⟨0,[],[false,true,true]++rep U (2*(2*m+3)+1)⟩ := by
    have eq : [false]++rep U 5++rep U (4*m+4) = [false,true,true]++rep U (2*(2*m+3)+1) := by
      rw [List.append_assoc,← rep_add]
      change [false]++rep U (5+(4*m+4)) = [false]++(rep U 2++rep U (2*(2*m+3)+1))
      rw [← rep_add]; congr 2; omega
    rw [← eq]; exact h2
  have h3 := pureStart (rep U (2*(2*m+3)+1))
  have h4 := rightSweep (2*m+3) [false,true,true]
  have h5 := finish (rep P (2*m+3)++[false,true,true])
  have H := join0 (join0 (join0 (join0 h1 h2') h3) h4) h5
  rw [show 12+10*m+7+5+2*(2*m+3)+3=14*m+33 by omega] at H
  have eq : P++(rep P (2*m+3)++[false,true,true]) = rep P (2*(m+1)+3)++[true] := by
    change rep P 1++(rep P (2*m+3)++(rep P 1++[true])) = _
    rw [← List.append_assoc (rep P (2*m+3)),← rep_add,← List.append_assoc,← rep_add]
    congr 2; omega
  rw [eq] at H
  simpa only [pure,extra] using H

def family (n : Nat) : Z0 := extra (2*n)
theorem entry : run0 table 25 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (56*n+76) (family n) = some (family (n+1)) := by
  have H := join0 (extraEpoch (2*n)) (pureEpoch (2*n+1))
  rw [show 14*(2*n)+29+(14*(2*n+1)+33)=56*n+76 by omega] at H
  simpa only [family,show 2*n+1+1=2*(n+1) by omega] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 25 (fun n => 56*n+76) entry (by omega) growth m hm
#print axioms never
end BB6.Agent19Raw40.LC1RDAlt
