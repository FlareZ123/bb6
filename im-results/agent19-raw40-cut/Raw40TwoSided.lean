import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40
open BB6Coverage BB6Coverage.Agent31Pump

private theorem rep_add (P : List Bool) (n m : Nat) :
    rep P (n+m) = rep P n ++ rep P m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m = (n+m)+1 by omega,rep,ih]; simp only [rep,List.append_assoc]

namespace RC1LB
-- 1RB0RC_1RC1RE_0RD1LB_1LD1LA_1LF0RF_---0LB
-- F0 is never queried.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
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
theorem entry : run0 table 61 ⟨0,[],[]⟩ = some (family 0) := by rfl

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
    run0 table 19 ⟨0,[false,true]++L,[true,true,true]⟩ =
      some ⟨0,[false,true,true,true,true]++L,[true]⟩ := by rfl

theorem turn (n : Nat) :
    run0 table 19 ⟨0,[false]++rep [true] (3*(n+1)+1),[true,true,true]⟩ =
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

theorem growth (n : Nat) : run0 table (16*n+57) (family n) = some (family (n+1)) := by
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
  rw [show 7*(n+1)+19+4+3*(3*n+8)+3=16*n+57 by omega,
      show 3*n+8+1=3*(n+1)+6 by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 61 (fun n => 16*n+57) entry (by omega) growth m hm
#print axioms never
end RC1LB

namespace RB0RC
-- 1RB0RB_1RC0RC_0RD0LE_1LD1LA_0LF---_1LC0RB
-- E1 is never queried.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],rep [true,true] (2*n+4)⟩
theorem entry : run0 table 71 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem firstRight (R : List Bool) :
    run0 table 8 ⟨0,[],[true,true,true]++R⟩ =
      some ⟨0,[false,true,false],true::R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 8 ⟨0,[false]++L,[true]++[true,true]++R⟩ =
      some ⟨0,[false]++[true,false]++L,[true]++R⟩ := by rfl

theorem rightSweep (n : Nat) :
    run0 table (8+8*(2*n+2)) (family n) =
      some ⟨0,[false]++rep [true,false] (2*n+3),[true,true]⟩ := by
  have h1 := firstRight (true::rep [true,true] (2*n+2))
  have h1' : run0 table 8 (family n) =
      some ⟨0,[false,true,false],[true]++rep [true,true] (2*n+2)++[true]⟩ := by
    unfold family
    rw [show 2*n+4=2+(2*n+2) by omega,rep_add]
    have eq : [true] ++ rep [true,true] (2*n+2) ++ [true] = true::true::rep [true,true] (2*n+2) := by
      rw [List.append_assoc]; change true :: (rep [true,true] (2*n+2) ++ [true]) = _
      rw [← show [true]++rep [true,true] (2*n+2) = rep [true,true] (2*n+2)++[true] from rotate true [true] _]; rfl
    rw [eq]
    exact h1
  have h2 := sweepR table 0 [false] [true] [true,true] [true,false] 8 rightOne (2*n+2) [true,false] [true]
  simp only [List.append_assoc] at h2
  rw [rep_snoc] at h2
  have H := join0 h1' h2
  exact H

theorem turnRight (L : List Bool) :
    run0 table 10 ⟨0,false::L,[true,true]⟩ =
      some ⟨0,false::L,[true,true,true]⟩ := by rfl

theorem firstLeft (L : List Bool) :
    run0 table 14 ⟨0,[false,true,false]++L,[true]⟩ =
      some ⟨0,false::L,[true,false,false,true,true]⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 14 ⟨0,[false]++[true,false]++L,[true,false,false]++R⟩ =
      some ⟨0,[false]++L,[true,false,false]++[true,true]++R⟩ := by rfl

theorem leftSweep (k : Nat) :
    run0 table (14*k) ⟨0,[false]++rep [true,false] k,[true,false,false,true,true]⟩ =
      some ⟨0,[false],[true,false,false]++rep [true,true] (k+1)⟩ := by
  have H := sweepL table 0 [false] [true,false,false] [true,false] [true,true] 14 leftOne k [] [true,true]
  simp only [List.append_nil,List.append_assoc] at H
  rw [rep_snoc] at H
  exact H

theorem restart (R : List Bool) :
    run0 table 7 ⟨0,[false],[true,false,false]++R⟩ =
      some ⟨0,[],[true,true,true,true]++R⟩ := by rfl

theorem growth (n : Nat) : run0 table (44*n+105) (family n) = some (family (n+1)) := by
  let k := 2*n+3
  have h1 := rightSweep n
  have h2 := turnRight (rep [true,false] k)
  have h3 := rightOne (rep [true,false] k) []
  have h4 := firstLeft (rep [true,false] k)
  have h5 := leftSweep k
  have h6 := restart (rep [true,true] (k+1))
  have H := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
  have ht : 8+8*(2*n+2)+10+8+14+14*k+7=44*n+105 := by dsimp [k]; omega
  rw [ht] at H
  have hfin : [true,true,true,true] ++ rep [true,true] (k+1) = rep [true,true] (2*(n+1)+4) := by
    rw [show 2*(n+1)+4=2+(k+1) by dsimp [k]; omega]
    exact (rep_add [true,true] 2 (k+1)).symm
  rw [hfin] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 71 (fun n => 44*n+105) entry (by omega) growth m hm
#print axioms never
end RB0RC
end BB6.Agent19Raw40
