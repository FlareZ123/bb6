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

-- Common partial table; only the B1 instruction differs.
def sweepTable (b : Move) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some b)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | _,_ => none

private theorem aOne (b : Move) (L R : List Bool) :
    run0 (sweepTable b) 1 ⟨0,[true]++L,R⟩ = some ⟨0,L,[true]++R⟩ := by rfl

private theorem aSweep (b : Move) (k : Nat) :
    run0 (sweepTable b) k ⟨0,rep [true] k,[true,true,true]⟩ =
      some ⟨0,[],rep [true] k++[true,true,true]⟩ := by
  simpa using sweepL (sweepTable b) 0 [] [] [true] [true] 1 (aOne b) k [] [true,true,true]

namespace RD
-- 1RB1LA_1RC0RD_0RD---_1LD1LA_------_------
abbrev table := sweepTable ⟨false,true,3⟩
def family (n : Nat) : Z0 := ⟨1,[true,true],rep [true] (2*n+3)⟩
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem bOne (L R : List Bool) :
    run0 table 3 ⟨1,[true]++L,[true]++R⟩ = some ⟨1,[true]++[true]++L,R⟩ := by rfl

theorem bSweep (k : Nat) :
    run0 table (3*k) ⟨1,[true,true],rep [true] k⟩ =
      some ⟨1,[true]++rep [true] k++[true],[]⟩ := by
  simpa using sweepR table 1 [true] [] [true] [true] 3 bOne k [true] []

theorem turn (k : Nat) :
    run0 table 4 ⟨1,[true]++rep [true] k++[true],[]⟩ =
      some ⟨0,rep [true] k,[true,true,true]⟩ := by
  rw [List.append_assoc,← show rep [true] (k+1) = rep [true] k++[true] from rep_add [true] k 1]
  rfl

theorem restart (k : Nat) :
    run0 table 1 ⟨0,[],rep [true] k++[true,true,true]⟩ =
      some ⟨1,[true,true],rep [true] (k+2)⟩ := by
  rw [← show rep [true] (k+3) = rep [true] k++[true,true,true] from rep_add [true] k 3]
  rfl

theorem growth (n : Nat) : run0 table (8*n+17) (family n) = some (family (n+1)) := by
  let k := 2*n+3
  have H := join0 (join0 (join0 (bSweep k) (turn k)) (aSweep ⟨false,true,3⟩ k)) (restart k)
  have ht : 3*k+4+k+1 = 8*n+17 := by dsimp [k]; omega
  have hn : k+2 = 2*(n+1)+3 := by dsimp [k]; omega
  rw [ht,hn] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 8*n+17) entry (by omega) growth m hm
#print axioms never
end RD

namespace RB
-- 1RB1LA_1RC1RB_0RD---_1LD1LA_------_------
abbrev table := sweepTable ⟨true,true,1⟩
def family (n : Nat) : Z0 := ⟨1,[true,true],rep [true] (4*n+3)⟩
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem bOne (L R : List Bool) :
    run0 table 1 ⟨1,[true]++L,[true]++R⟩ = some ⟨1,[true]++[true]++L,R⟩ := by rfl

theorem bSweep (k : Nat) :
    run0 table k ⟨1,[true,true],rep [true] k⟩ =
      some ⟨1,[true]++rep [true] k++[true],[]⟩ := by
  simpa using sweepR table 1 [true] [] [true] [true] 1 bOne k [true] []

theorem turn (k : Nat) :
    run0 table 6 ⟨1,[true]++rep [true] k++[true],[]⟩ =
      some ⟨0,rep [true] (k+2),[true,true,true]⟩ := by
  rw [List.append_assoc,← show rep [true] (k+1) = rep [true] k++[true] from rep_add [true] k 1]
  rfl

theorem restart (k : Nat) :
    run0 table 1 ⟨0,[],rep [true] (k+2)++[true,true,true]⟩ =
      some ⟨1,[true,true],rep [true] (k+4)⟩ := by
  rw [← show rep [true] (k+2+3) = rep [true] (k+2)++[true,true,true] from rep_add [true] (k+2) 3]
  rfl

theorem growth (n : Nat) : run0 table (8*n+15) (family n) = some (family (n+1)) := by
  let k := 4*n+3
  have H := join0 (join0 (join0 (bSweep k) (turn k)) (aSweep ⟨true,true,1⟩ (k+2))) (restart k)
  have ht : k+6+(k+2)+1 = 8*n+15 := by dsimp [k]; omega
  have hn : k+4 = 4*(n+1)+3 := by dsimp [k]; omega
  rw [ht,hn] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 8*n+15) entry (by omega) growth m hm
#print axioms never
end RB
end BB6.Agent19Raw40
