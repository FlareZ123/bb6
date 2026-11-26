import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Leaf236
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1RC_1RC1RE_0RD0LB_1LD1LA_1LC1RF_---1RB
-- F0 is never queried.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

def u (n : Nat) := rep [true] n
private theorem uadd (a b : Nat) : u (a+b) = u a ++ u b := by
  induction a with
  | zero => simp [u,rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    change [true] ++ u (a+b) = ([true] ++ u a) ++ u b
    rw [ih,List.append_assoc]
private theorem triple (n : Nat) : rep [true,true,true] n = u (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show 3*(n+1)=3+3*n by omega,uadd]; rfl

def family (n : Nat) : Z0 := ⟨1,[],false::u (6*n+3)⟩
def mid (n : Nat) : Z0 := ⟨1,[],false::u (6*n+7)⟩
theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem enter (R : List Bool) :
  run0 table 4 ⟨1,[],false::true::R⟩ = some ⟨1,[true,true,true],R⟩ := by rfl

theorem rightOne (L R : List Bool) :
  run0 table 3 ⟨1,[true]++L,[true,true,true]++R⟩ = some ⟨1,[true]++[true,true,true]++L,R⟩ := by rfl

theorem leftOne (L R : List Bool) :
  run0 table 3 ⟨1,[true]++L,[false]++R⟩ = some ⟨1,L,[false]++[true]++R⟩ := by rfl

theorem turnA (L : List Bool) :
  run0 table 10 ⟨1,true::L,[true,true]⟩ = some ⟨1,[true,true,true]++L,[false,true,true]⟩ := by rfl

theorem turnB (L : List Bool) :
  run0 table 3 ⟨1,true::L,[]⟩ = some ⟨1,L,[false,true]⟩ := by rfl

theorem sweepRight (k : Nat) (R : List Bool) :
  run0 table (3*k) ⟨1,u 3,u (3*k)++R⟩ = some ⟨1,u (3*k+3),R⟩ := by
  have H := sweepR table 1 [true] [] [true,true,true] [true,true,true] 3 rightOne k [true,true] R
  rw [triple] at H
  simp only [List.nil_append,List.append_assoc] at H
  have e : [true] ++ (u (3*k) ++ [true,true]) = u (3*k+3) := by
    calc
      [true] ++ (u (3*k) ++ [true,true]) = u 1 ++ (u (3*k) ++ u 2) := rfl
      _ = u (1+(3*k+2)) := by rw [← uadd (3*k) 2, ← uadd 1 (3*k+2)]
      _ = u (3*k+3) := by congr 1 <;> omega
  rw [e] at H
  exact H

theorem sweepLeft (k j : Nat) :
  run0 table (3*k) ⟨1,u k,false::u j⟩ = some ⟨1,[],false::u (k+j)⟩ := by
  have H := sweepL table 1 [] [false] [true] [true] 3 leftOne k [] (u j)
  simp only [List.nil_append,List.append_nil,List.append_assoc] at H
  change run0 table (3*k) ⟨1,u k,false::u j⟩ = some ⟨1,[],false::(u k++u j)⟩ at H
  rw [← uadd] at H
  exact H

theorem phaseA (n : Nat) : run0 table (24*n+29) (family n) = some (mid n) := by
  have h1 := enter (u (6*n+2))
  have h1' : run0 table 4 (family n) = some ⟨1,u 3,u (6*n+2)⟩ := by
    unfold family; rw [show 6*n+3=1+(6*n+2) by omega,uadd]; exact h1
  have h2 := sweepRight (2*n) [true,true]
  have h2' : run0 table (3*(2*n)) ⟨1,u 3,u (6*n+2)⟩ = some ⟨1,u (6*n+3),[true,true]⟩ := by
    rw [show 6*n+2=3*(2*n)+2 by omega,uadd]
    rw [show u 2 = [true,true] by rfl]
    simpa only [show 3*(2*n)+3=6*n+3 by omega] using h2
  have h3 := turnA (u (6*n+2))
  have h3' : run0 table 10 ⟨1,u (6*n+3),[true,true]⟩ = some ⟨1,u (6*n+5),[false,true,true]⟩ := by
    rw [show 6*n+3=1+(6*n+2) by omega,uadd 1 (6*n+2),show 6*n+5=3+(6*n+2) by omega,uadd 3 (6*n+2)]
    exact h3
  have h4 := sweepLeft (6*n+5) 2
  have H := join0 (join0 (join0 h1' h2') h3') h4
  rw [show 4+3*(2*n)+10+3*(6*n+5)=24*n+29 by omega,show 6*n+5+2=6*n+7 by omega] at H
  exact H

theorem phaseB (n : Nat) : run0 table (24*n+37) (mid n) = some (family (n+1)) := by
  have h1 := enter (u (6*n+6))
  have h1' : run0 table 4 (mid n) = some ⟨1,u 3,u (6*n+6)⟩ := by
    unfold mid; rw [show 6*n+7=1+(6*n+6) by omega,uadd]; exact h1
  have h2 := sweepRight (2*n+2) []
  have h2' : run0 table (3*(2*n+2)) ⟨1,u 3,u (6*n+6)⟩ = some ⟨1,u (6*n+9),[]⟩ := by
    simpa only [List.append_nil,show 3*(2*n+2)=6*n+6 by omega,show 6*n+6+3=6*n+9 by omega] using h2
  have h3 := turnB (u (6*n+8))
  have h3' : run0 table 3 ⟨1,u (6*n+9),[]⟩ = some ⟨1,u (6*n+8),[false,true]⟩ := by
    rw [show 6*n+9=1+(6*n+8) by omega,uadd]; exact h3
  have h4 := sweepLeft (6*n+8) 1
  have H := join0 (join0 (join0 h1' h2') h3') h4
  rw [show 4+3*(2*n+2)+3+3*(6*n+8)=24*n+37 by omega,show 6*n+8+1=6*(n+1)+3 by omega] at H
  exact H

theorem growth (n : Nat) : run0 table (48*n+66) (family n) = some (family (n+1)) := by
  have H := join0 (phaseA n) (phaseB n)
  rwa [show 24*n+29+(24*n+37)=48*n+66 by omega] at H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 (fun n => 48*n+66) entry (by omega) growth m hm
#print axioms never
end BB6.Agent19Raw40.Leaf236
