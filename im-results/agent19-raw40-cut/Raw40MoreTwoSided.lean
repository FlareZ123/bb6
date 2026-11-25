import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40
open BB6Coverage BB6Coverage.Agent31Pump

namespace RB1RC
-- 1RB0RB_1RC1RC_0RD0LE_1LD1LA_---1LF_1LC0RF
-- E0 is never queried.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def block : List Bool := [true,true,false]
def family (n : Nat) : Z0 := ⟨0,[false],rep block (n+1)++[true]⟩
theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem rightOne (L R : List Bool) :
  run0 table 13 ⟨0,[false]++L,block++[true]++R⟩ = some ⟨0,[false]++block++L,[true]++R⟩ := by rfl

theorem rightSweep (k : Nat) (L : List Bool) :
    run0 table (13*k) ⟨0,[false]++L,rep block k++[true]⟩ =
      some ⟨0,[false]++rep block k++L,[true]⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 13 ⟨0,[false]++L,rep block (k+1)++[true]⟩ =
        some ⟨0,[false]++block++L,rep block k++[true]⟩ := by
      cases k <;> rfl
    have H := join0 h (ih (block++L))
    rw [show 13*(k+1)=13+13*k by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep block k) block L,rep_snoc block k] using H

theorem turn (L : List Bool) :
  run0 table 8 ⟨0,[false]++block++L,[true]⟩ = some ⟨2,block++block++L,[true]⟩ := by rfl

theorem leftOne (L R : List Bool) :
  run0 table 3 ⟨2,block++L,R⟩ = some ⟨2,L,block++R⟩ := by rfl

theorem restart (R : List Bool) :
  run0 table 2 ⟨2,[],true::R⟩ = some ⟨0,[false],true::R⟩ := by rfl

theorem growth (n : Nat) : run0 table (16*n+29) (family n) = some (family (n+1)) := by
  have h1 := rightSweep (n+1) []
  simp only [List.nil_append,List.append_nil] at h1
  have h2 := turn (rep block n)
  have h2' : run0 table 8 ⟨0,[false]++rep block (n+1),[true]⟩ = some ⟨2,rep block (n+2),[true]⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3 := sweepL table 2 [] [] block block 3 leftOne (n+2) [] [true]
  simp only [List.nil_append,List.append_nil] at h3
  have h4 := restart (true::false::rep block (n+1)++[true])
  have h4' : run0 table 2 ⟨2,[],rep block (n+2)++[true]⟩ = some (family (n+1)) := by
    simpa only [family,rep,List.append_assoc,block,List.cons_append,List.nil_append] using h4
  have H := join0 (join0 (join0 h1 h2') h3) h4'
  rw [show 13*(n+1)+8+3*(n+2)+2=16*n+29 by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun n => 16*n+29) entry (by omega) growth m hm
#print axioms never
end RB1RC

namespace A10RC
-- Two A1 variants, common sweep: 1RB1RB/1RB0RD, F0 unqueried.
def table (a : Move) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some a)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def block : List Bool := [true,true,false]
def unary : List Bool := [true,true,true]
def family (n : Nat) : Z0 := ⟨0,[false],rep block (n+2)++[true]⟩
def rb : Move := ⟨true,true,1⟩
def rd : Move := ⟨false,true,3⟩
theorem entryRB : run0 (table rb) 49 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem entryRD : run0 (table rd) 53 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem rightOne (a : Move) (L R : List Bool) :
  run0 (table a) 7 ⟨0,[false]++L,block++[true]++R⟩ = some ⟨0,[false]++unary++L,[true]++R⟩ := by rfl

theorem rightSweep (a : Move) (k : Nat) (L : List Bool) :
    run0 (table a) (7*k) ⟨0,[false]++L,rep block k++[true]⟩ =
      some ⟨0,[false]++rep unary k++L,[true]⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h : run0 (table a) 7 ⟨0,[false]++L,rep block (k+1)++[true]⟩ =
        some ⟨0,[false]++unary++L,rep block k++[true]⟩ := by
      cases k <;> rfl
    have H := join0 h (ih (unary++L))
    rw [show 7*(k+1)=7+7*k by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep unary k) unary L,rep_snoc unary k] using H

theorem turnRB (L : List Bool) :
  run0 (table rb) 12 ⟨0,[false]++unary++L,[true]⟩ = some ⟨2,unary++unary++L,[true]⟩ := by rfl

theorem turnRD (L : List Bool) :
  run0 (table rd) 14 ⟨0,[false]++unary++L,[true]⟩ = some ⟨2,unary++unary++L,[true]⟩ := by rfl

theorem leftOne (a : Move) (L R : List Bool) :
  run0 (table a) 3 ⟨2,unary++L,R⟩ = some ⟨2,L,block++R⟩ := by rfl

theorem restart (a : Move) (R : List Bool) :
  run0 (table a) 2 ⟨2,[],true::R⟩ = some ⟨0,[false],true::R⟩ := by rfl

theorem growth (a : Move) (t : Nat)
    (turn : ∀ L : List Bool, run0 (table a) t ⟨0,[false]++unary++L,[true]⟩ = some ⟨2,unary++unary++L,[true]⟩)
    (n : Nat) : run0 (table a) (10*n+t+25) (family n) = some (family (n+1)) := by
  have h1 := rightSweep a (n+2) []
  simp only [List.nil_append,List.append_nil] at h1
  have h2 := turn (rep unary (n+1))
  have h2' : run0 (table a) t ⟨0,[false]++rep unary (n+2),[true]⟩ = some ⟨2,rep unary (n+3),[true]⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h3 := sweepL (table a) 2 [] [] unary block 3 (leftOne a) (n+3) [] [true]
  simp only [List.nil_append,List.append_nil] at h3
  have h4 := restart a (true::false::rep block (n+2)++[true])
  have h4' : run0 (table a) 2 ⟨2,[],rep block (n+3)++[true]⟩ = some (family (n+1)) := by
    simpa only [family,rep,List.append_assoc,block,List.cons_append,List.nil_append] using h4
  have H := join0 (join0 (join0 h1 h2') h3) h4'
  rw [show 7*(n+2)+t+3*(n+3)+2=10*n+t+25 by omega] at H
  exact H

theorem neverRB (m : Machine) (hm : compatible (table rb) m) : NeverHalts m :=
  never_of_growth (table rb) family 49 (fun n => 10*n+12+25) entryRB (by omega) (growth rb 12 turnRB) m hm

theorem neverRD (m : Machine) (hm : compatible (table rd) m) : NeverHalts m :=
  never_of_growth (table rd) family 53 (fun n => 10*n+14+25) entryRD (by omega) (growth rd 14 turnRD) m hm
#print axioms neverRB
#print axioms neverRD
end A10RC
private theorem rep_add (P : List Bool) (n m : Nat) :
    rep P (n+m) = rep P n ++ rep P m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m = (n+m)+1 by omega,rep,ih]; simp only [rep,List.append_assoc]

namespace OneRC1LB
-- 1RB1RC_1RC1RE_0RD1LB_1LD1LA_1LF0RF_---0LB
-- F0 is never queried.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[false,true],rep [true] (3*n+6)⟩
theorem entry : run0 table 59 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 7 ⟨0,[false]++L,[true]++[true,true,true]++R⟩ =
      some ⟨0,[false]++[true,true,true]++L,[true]++R⟩ := by rfl

private theorem rep3 (k : Nat) : rep [true,true,true] k = rep [true] (3*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,show 3*(k+1)=3+3*k by omega,rep_add]; rfl

theorem rightSweep (n : Nat) :
    run0 table (7*(n+1)) (family n) =
      some ⟨0,[false]++rep [true] (3*(n+1)+1),[true,true,true]⟩ := by
  have H := sweepR table 0 [false] [true] [true,true,true] [true,true,true] 7 rightOne (n+1) [true] [true,true]
  rw [rep3] at H
  simp only [List.append_assoc] at H
  have e1 : [true] ++ (rep [true] (3*(n+1)) ++ [true,true]) = rep [true] (3*n+6) := by
    rw [← show rep [true] (3*(n+1)+2) = rep [true] (3*(n+1))++[true,true] from rep_add [true] _ 2]
    rw [show 3*n+6=1+(3*(n+1)+2) by omega]
    exact (rep_add [true] 1 (3*(n+1)+2)).symm
  have e2 : rep [true] (3*(n+1)) ++ [true] = rep [true] (3*(n+1)+1) := (rep_add [true] _ 1).symm
  rw [e1,e2] at H
  exact H

theorem turnOne (L : List Bool) :
    run0 table 17 ⟨0,[false,true]++L,[true,true,true]⟩ =
      some ⟨0,[false,true,true,true,true]++L,[true]⟩ := by rfl

theorem turn (n : Nat) :
    run0 table 17 ⟨0,[false]++rep [true] (3*(n+1)+1),[true,true,true]⟩ =
      some ⟨0,[false]++rep [true] (3*n+7),[true]⟩ := by
  have H := turnOne (rep [true] (3*(n+1)))
  rw [show 3*(n+1)+1 = 1+3*(n+1) by omega,show 3*n+7=4+3*(n+1) by omega,rep_add,rep_add]
  exact H

theorem startLeft (L : List Bool) :
    run0 table 4 ⟨0,false::L,[true]⟩ = some ⟨1,true::L,[false,true]⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 3 ⟨1,[true]++L,[false]++R⟩ = some ⟨1,L,[false]++[true]++R⟩ := by rfl

theorem leftSweep (k : Nat) :
    run0 table (3*k) ⟨1,rep [true] k,[false,true]⟩ =
      some ⟨1,[],[false]++rep [true] (k+1)⟩ := by
  have H := sweepL table 1 [] [false] [true] [true] 3 leftOne k [] [true]
  simp only [List.nil_append,List.append_nil] at H
  simp only [List.append_assoc] at H
  rw [← show rep [true] (k+1) = rep [true] k ++ [true] from rep_add [true] k 1] at H
  exact H

theorem restart (R : List Bool) :
    run0 table 3 ⟨1,[],false::true::R⟩ = some ⟨0,[false,true],true::R⟩ := by rfl

theorem growth (n : Nat) : run0 table (16*n+55) (family n) = some (family (n+1)) := by
  have h1 := rightSweep n
  have h2 := turn n
  have h3 := startLeft (rep [true] (3*n+7))
  have h4 := leftSweep (3*n+8)
  have h5 := restart (rep [true] (3*n+8))
  have h3' : run0 table 4 ⟨0,[false]++rep [true] (3*n+7),[true]⟩ =
      some ⟨1,rep [true] (3*n+8),[false,true]⟩ := by
    rw [show 3*n+8=1+(3*n+7) by omega,show rep [true] (1+(3*n+7)) = [true]++rep [true] (3*n+7) from rep_add [true] 1 _]; exact h3
  have h5' : run0 table 3 ⟨1,[],[false]++rep [true] (3*n+8+1)⟩ = some ⟨0,[false,true],rep [true] (3*n+8+1)⟩ := by
    rw [show 3*n+8+1=1+(3*n+8) by omega,show rep [true] (1+(3*n+8)) = [true]++rep [true] (3*n+8) from rep_add [true] 1 _]; exact h5
  have H := join0 (join0 (join0 (join0 h1 h2) h3') h4) h5'
  rw [show 7*(n+1)+17+4+3*(3*n+8)+3=16*n+55 by omega,
      show 3*n+8+1=3*(n+1)+6 by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 59 (fun n => 16*n+55) entry (by omega) growth m hm
#print axioms never
end OneRC1LB

end BB6.Agent19Raw40
