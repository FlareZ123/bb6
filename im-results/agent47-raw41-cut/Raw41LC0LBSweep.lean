import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LC0LB
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LC_1RC1LE_0RD0LB_1LD1RA_1RF---_0RB0RF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def P : List Bool := [false,true,true]
def Z : List Bool := [false]
def U : List Bool := [true]
def family (n : Nat) : Z0 := ⟨4,[false,true]++rep P n,[true,false,false]++rep U (n+3)⟩

theorem entry : run0 table 40 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem start (L R : List Bool) :
    run0 table 10 ⟨4,[false,true]++L,[true,false,false,true,true]++R⟩ =
      some ⟨4,[false,false,true]++P++L,[true]++R⟩ := by rfl

theorem enterF (L R : List Bool) :
    run0 table 1 ⟨4,[false,false,true]++L,[true]++R⟩ =
      some ⟨5,[true,true,false,true]++L,R⟩ := by rfl

theorem fOne (L R : List Bool) :
    run0 table 1 ⟨5,[true]++L,[true]++R⟩ = some ⟨5,[true,false]++L,R⟩ := by rfl

theorem fFinish (L : List Bool) :
    run0 table 2 ⟨5,[true]++L,[]⟩ = some ⟨1,[false,false,false]++L,[]⟩ := by rfl

theorem bStart (L : List Bool) :
    run0 table 7 ⟨1,[false,false]++L,[]⟩ = some ⟨1,[false]++L,[false,false,true]⟩ := by rfl

theorem bOne (L R : List Bool) :
    run0 table 7 ⟨1,[false]++L,[false,false]++R⟩ = some ⟨1,L,[false,false,true]++R⟩ := by rfl

theorem bFinish (L R : List Bool) :
    run0 table 1 ⟨1,[true,false,true]++L,[false,false]++R⟩ =
      some ⟨4,[false,true]++L,[true,false,false]++R⟩ := by rfl
private theorem rep_add (p : List Bool) (n m : Nat) : rep p (n+m) = rep p n ++ rep p m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=(n+m)+1 by omega,rep,ih]; simp only [rep,List.append_assoc]

theorem growth (n : Nat) : run0 table (8*n+43) (family n) = some (family (n+1)) := by
  have h1 := start (rep P n) (rep U (n+1))
  have h1' : run0 table 10 (family n) = some ⟨4,[false,false,true]++rep P (n+1),rep U (n+2)⟩ := by
    exact h1
  have h2 := enterF (rep P (n+1)) (rep U (n+1))
  have h2' : run0 table 1 ⟨4,[false,false,true]++rep P (n+1),rep U (n+2)⟩ =
      some ⟨5,[true]++([true,false,true]++rep P (n+1)),rep U (n+1)⟩ := by
    exact h2
  have h3 := sweepR table 5 [true] [] U Z 1 fOne (n+1) ([true,false,true]++rep P (n+1)) []
  simp only [List.nil_append,List.append_nil,Nat.one_mul] at h3
  have h4 := fFinish (rep Z (n+1)++([true,false,true]++rep P (n+1)))
  have h4' : run0 table 2 ⟨5,[true]++rep Z (n+1)++([true,false,true]++rep P (n+1)),[]⟩ =
      some ⟨1,rep Z (n+4)++([true,false,true]++rep P (n+1)),[]⟩ := by
    exact h4
  have h5 := bStart (rep Z (n+2)++([true,false,true]++rep P (n+1)))
  have h5' : run0 table 7 ⟨1,rep Z (n+4)++([true,false,true]++rep P (n+1)),[]⟩ =
      some ⟨1,rep Z (n+3)++([true,false,true]++rep P (n+1)),[false,false]++rep U 1⟩ := by
    exact h5
  have h6 := sweepL table 1 [] [false,false] Z U 7 bOne (n+3) ([true,false,true]++rep P (n+1)) (rep U 1)
  simp only [List.nil_append,List.append_assoc] at h6
  rw [← rep_add] at h6
  have h7 := bFinish (rep P (n+1)) (rep U (n+4))
  have H := join0 (join0 (join0 (join0 (join0 (join0 h1' h2') h3) h4') h5') h6) h7
  rw [show 10+1+(n+1)+2+7+7*(n+3)+1=8*n+43 by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 40 (fun n => 8*n+43) entry (by omega) growth m hm
#print axioms never
end BB6.Agent47Raw41.LC0LB
