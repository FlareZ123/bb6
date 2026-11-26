import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Round43NestedRB
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1RB_1RC0LE_0RD0RC_1LD1LA_---1LF_1LB0RF; E0 is unassigned.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def U (n : Nat) := rep [true] n
def Z (n : Nat) := rep [false] n
private theorem repAdd (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=(a+b)+1 by omega,rep,ih,rep,List.append_assoc]

theorem bFirst (R : List Bool) : run0 table 9 ⟨1,[],[true,true,false,true]++R⟩ =
    some ⟨1,[false,true],[true,true,false]++R⟩ := by rfl

theorem bMove (L R : List Bool) : run0 table 9 ⟨1,[false]++L,[true,true,false]++[true]++R⟩ =
    some ⟨1,[false]++[true]++L,[true,true,false]++R⟩ := by rfl

theorem bTurn (L : List Bool) : run0 table 4 ⟨1,[false]++L,[true,true,false]⟩ =
    some ⟨3,[false,false,false,false,true]++L,[]⟩ := by rfl

theorem prep (m : Nat) : run0 table (9+9*m+4) ⟨1,[],[true,true,false]++U (m+1)⟩ =
    some ⟨3,Z 4 ++ U (m+2),[]⟩ := by
  have h1 := bFirst (U m)
  have h2 := sweepR table 1 [false] [true,true,false] [true] [true] 9 bMove m [true] []
  have h3 := bTurn (U m ++ [true])
  simp only [List.append_nil,List.singleton_append] at h2
  have H := join0 (join0 h1 h2) h3
  have hc : rep [true] m ++ [true] = true :: rep [true] m := by
    exact (repAdd [true] m 1).symm
  change run0 table _ _ = some ⟨3,[false,false,false,false,true] ++ (rep [true] m ++ [true]),[]⟩ at H
  rw [hc] at H
  simpa only [U,Z,repAdd,show rep [true] 1=[true] by rfl,show rep [true] 2=[true,true] by rfl,
    show rep [false] 4=[false,false,false,false] by rfl,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,
    show m+1=1+m by omega,show m+2=1+(m+1) by omega] using H

theorem dInitial (L : List Bool) : run0 table 18 ⟨3,[false,false,false,false,true,true,true]++L,[]⟩ =
    some ⟨3,[false,false,false,false,false,false,false,true,false]++L,[]⟩ := by rfl

theorem dMove (L R : List Bool) : run0 table 1 ⟨3,[false]++L,R⟩ = some ⟨3,L,[true]++R⟩ := by rfl

theorem cMove (L R : List Bool) : run0 table 1 ⟨2,[true]++L,[true]++R⟩ =
    some ⟨2,[true]++[false]++L,R⟩ := by rfl

theorem mid (L R : List Bool) : run0 table 8 ⟨3,[true,false,true]++L,[true]++R⟩ =
    some ⟨2,[true,true,false]++L,[true]++R⟩ := by rfl

theorem cTurn (L : List Bool) : run0 table 2 ⟨2,[true]++L,[]⟩ = some ⟨3,[false,false,false]++L,[]⟩ := by rfl

def inner (a k : Nat) : Z0 := ⟨3,Z a ++ [true,false] ++ U k,[]⟩
def family (m : Nat) : Z0 := ⟨1,[],[true,true,false]++U m⟩

theorem epoch (a k : Nat) : run0 table (2*(a+1)+10) (inner (a+1) (k+1)) = some (inner (a+4) k) := by
  have h1 := sweepL table 3 [] [] [false] [true] 1 dMove (a+1) ([true,false,true]++U k) []
  simp only [List.nil_append,List.append_nil] at h1
  have h2 := mid (U k) (U a)
  have h3 := sweepR table 2 [true] [] [true] [false] 1 cMove (a+1) ([true,false]++U k) []
  simp only [List.nil_append,List.append_nil] at h3
  have h4 := cTurn (Z (a+1)++[true,false]++U k)
  simp only [Z,List.append_assoc] at h3 h4
  have H := join0 (join0 (join0 h1 h2) h3) h4
  simpa only [inner,U,Z,repAdd,show rep [true] 1=[true] by rfl,
    show rep [false] 3=[false,false,false] by rfl,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,
    show k+1=1+k by omega,show a+1=1+a by omega,show a+4=3+(a+1) by omega,
    show 1*(1+a)+8+1*(1+a)+2=2*(1+a)+10 by omega] using H

theorem last (R : List Bool) : run0 table 5 ⟨3,[true,false],[true]++R⟩ =
    some ⟨1,[],[true,true,false,true]++R⟩ := by rfl

theorem finish (a : Nat) : run0 table (a+1+5) (inner (a+1) 0) = some (family (a+1)) := by
  have h1 := sweepL table 3 [] [] [false] [true] 1 dMove (a+1) [true,false] []
  simp only [List.nil_append,List.append_nil] at h1
  have H := join0 h1 (last (U a))
  simpa only [inner,family,U,Z,repAdd,rep,List.append_nil,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,List.cons_append,List.nil_append,
    Nat.one_mul] using H

def cost (a : Nat) : Nat → Nat
  | 0 => a+1+5
  | k+1 => 2*(a+1)+10+cost (a+3) k

theorem collapse (a k : Nat) : run0 table (cost a k) (inner (a+1) k) = some (family (a+1+3*k)) := by
  induction k generalizing a with
  | zero => simpa [cost] using finish a
  | succ k ih =>
    have H := join0 (epoch a k) (ih (a+3))
    simpa only [cost,show a+3+1=a+4 by omega,show a+3+1+3*k=a+1+3*(k+1) by omega] using H

def outerCost (k : Nat) := 9+9*(k+1)+4+18+cost 6 k

theorem grow (k : Nat) : run0 table (outerCost k) (family (k+2)) = some (family (3*k+7)) := by
  have h1 := prep (k+1)
  have h2 := dInitial (U k)
  have h2' : run0 table 18 ⟨3,Z 4 ++ U (k+3),[]⟩ = some (inner 7 k) := by
    rw [show k+3=3+k by omega,U,repAdd]
    simpa only [inner,Z,U,show rep [true] 3=[true,true,true] by rfl,
      show rep [false] 4=[false,false,false,false] by rfl,
      show rep [false] 7=[false,false,false,false,false,false,false] by rfl,List.append_assoc,List.cons_append,List.nil_append] using h2
  have h3 := collapse 6 k
  have H := join0 (join0 h1 h2') h3
  simpa only [outerCost,family,show k+1+1=k+2 by omega,show 6+1+3*k=3*k+7 by omega] using H

def idx : Nat → Nat
  | 0 => 0
  | n+1 => 3*idx n+5

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table (fun n => family (idx n+2)) 10 (fun n => outerCost (idx n)) _ _ _ m hm
  · rfl
  · intro n; unfold outerCost; omega
  · intro n
    simpa only [idx,show ∀ k : Nat, 3*k+5+2=3*k+7 by omega] using grow (idx n)

#print axioms collapse
#print axioms grow
#print axioms never
end BB6.Agent19Raw40.Round43NestedRB
