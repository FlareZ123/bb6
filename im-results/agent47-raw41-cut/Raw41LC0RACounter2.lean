import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LC0RA2New
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LC_1RC0LE_0RD0RA_1LD1RA_1LB1LF_0LB---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def P : List Bool := [true,false,true]
def Q : List Bool := [false,false,true]
def Rb : List Bool := [false,true,false]
def AP : List Bool := [false,false,true]
def GP : List Bool := [true,false,true,false,true]
def F (k : Nat) : Z0 := ⟨4,rep P (k+1),[false]⟩
def G (k : Nat) : Z0 := ⟨4,GP++rep P (k+1),[false]⟩
def family (n : Nat) : Z0 := F (4*n)

theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem leftOne (L R : List Bool) : run0 table 3 ⟨4,P++L,R⟩ = some ⟨4,L,Q++R⟩ := by rfl

theorem rightStart (R : List Bool) : run0 table 3 ⟨4,[],Q++R⟩ = some ⟨0,AP,[false,true]++R⟩ := by rfl

theorem rightOne (L R : List Bool) : run0 table 3 ⟨0,AP++L,Rb++R⟩ = some ⟨0,AP++P++L,R⟩ := by rfl

theorem finishF (L : List Bool) : run0 table 10 ⟨0,AP++L,[]⟩ = some ⟨4,GP++L,[false]⟩ := by rfl

theorem startG (L : List Bool) : run0 table 5 ⟨4,GP++L,[false]⟩ = some ⟨4,L,[false,true,false,false,true,false]⟩ := by rfl

theorem middleG (L : List Bool) : run0 table 2 ⟨0,AP++L,[true,false,false,true,false]⟩ = some ⟨4,P++L,[false,false,false,true,false]⟩ := by rfl

theorem finishG (L : List Bool) : run0 table 14 ⟨0,AP++L,[false,false,true,false]⟩ = some ⟨4,P++P++P++L,[false]⟩ := by rfl

theorem rotateQ (n : Nat) : [false,true]++rep Q n = rep Rb n++[false,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Rb ++ ([false,true] ++ rep Q n) = Rb ++ (rep Rb n ++ [false,true])
    rw [ih]

/-- Consume an arbitrary positive P block, reverse it, and restore it with an A-prefix. -/
theorem sweepRound (k : Nat) (S T : List Bool)
    (hS : [false,true]++S = Rb++T) :
    run0 table (6*(k+1)+3) ⟨4,rep P (k+1),S⟩ = some ⟨0,AP++rep P (k+1),T⟩ := by
  have h1 := sweepL table 4 [] [] P Q 3 leftOne (k+1) [] S
  simp only [List.nil_append,List.append_nil] at h1
  have h2 := rightStart (rep Q k++S)
  have h2' : run0 table 3 ⟨4,[],rep Q (k+1)++S⟩ = some ⟨0,AP,rep Rb (k+1)++T⟩ := by
    rw [show rep Q (k+1)++S = Q++(rep Q k++S) by simp only [rep,List.append_assoc]]
    have e : [false,true]++(rep Q k++S) = rep Rb (k+1)++T := by
      rw [← List.append_assoc,rotateQ,List.append_assoc,hS,← List.append_assoc,rep_snoc]
      rfl
    rw [e] at h2
    exact h2
  have h3 := sweepR table 0 AP [] Rb P 3 rightOne (k+1) [] T
  simp only [List.nil_append,List.append_nil] at h3
  have H := join0 (join0 h1 h2') h3
  rw [show 3*(k+1)+3+3*(k+1)=6*(k+1)+3 by omega] at H
  exact H

theorem F_to_G (k : Nat) : run0 table (6*(k+1)+13) (F k) = some (G k) := by
  have h1 := sweepRound k [false] [] (by rfl)
  have h2 := finishF (rep P (k+1))
  have H := join0 h1 h2
  rw [show 6*(k+1)+3+10=6*(k+1)+13 by omega] at H
  exact H

theorem G_to_F (k : Nat) : run0 table (12*(k+1)+33) (G k) = some (F (k+4)) := by
  have h1 := startG (rep P (k+1))
  have h2 := sweepRound k [false,true,false,false,true,false] [true,false,false,true,false] (by rfl)
  have h3 := middleG (rep P (k+1))
  have h3' : run0 table 2 ⟨0,AP++rep P (k+1),[true,false,false,true,false]⟩ = some ⟨4,rep P (k+2),[false,false,false,true,false]⟩ := h3
  have h4 := sweepRound (k+1) [false,false,false,true,false] [false,false,true,false] (by rfl)
  have h5 := finishG (rep P (k+2))
  have h5' : run0 table 14 ⟨0,AP++rep P (k+2),[false,false,true,false]⟩ = some (F (k+4)) := by
    exact h5
  have H := join0 (join0 (join0 (join0 h1 h2) h3') h4) h5'
  rw [show 5+(6*(k+1)+3)+2+(6*(k+1+1)+3)+14=12*(k+1)+33 by omega] at H
  exact H

theorem growth (n : Nat) : run0 table (72*n+64) (family n) = some (family (n+1)) := by
  have H := join0 (F_to_G (4*n)) (G_to_F (4*n))
  rw [show 6*(4*n+1)+13+(12*(4*n+1)+33)=72*n+64 by omega,
      show 4*n+4=4*(n+1) by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => 72*n+64) entry (by omega) growth m hm
#print axioms never
end BB6.Agent47Raw41.LC0RA2New
