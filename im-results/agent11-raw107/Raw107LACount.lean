import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw107LACount
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
abbrev U := [true]
abbrev Z := [false]
abbrev P := [false,false,true,false]
abbrev B (n : Nat) : Z0 := ⟨1,[false,false]++rep U n,[]⟩
abbrev D (L R : List Bool) : Z0 := ⟨3,P++L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩

theorem B_start (n : Nat) : run0 table 2 (B n) = some (D (rep U n) []) := by rfl

theorem D_one (L R : List Bool) : run0 table 13 (D (U++L) R) = some (D L (U++R)) := by rfl

theorem D_many (n : Nat) : run0 table (13*n) (D (rep U n) []) = some (D [] (rep U n)) := by
  simpa only [D,List.nil_append,List.append_nil,List.append_assoc] using sweepL table 3 P [] U U 13 D_one n [] []

theorem D_end (R : List Bool) : run0 table 10 (D [] R) = some (E [] ([false,false,false,true]++R)) := by rfl

theorem E_scan_one (L R : List Bool) : run0 table 1 (E (Z++L) (Z++R)) = some (E (Z++U++L) R) := by rfl

theorem E_scan_from (n : Nat) (L R : List Bool) : run0 table (n+1) (E (Z++L) (rep Z n++true::R)) = some (E (true::(rep U (n+1)++L)) R) := by
  have h := sweepR table 4 Z [] Z U 1 E_scan_one n L (true::R)
  simp only [List.nil_append,Nat.one_mul] at h
  have h1 : run0 table 1 (E (Z++rep U n++L) (true::R)) = some (E (true::true::(rep U n++L)) R) := by rfl
  exact join0 h h1

theorem E_scan (n : Nat) (R : List Bool) : run0 table (n+1) (E [] (rep Z n++true::R)) = some (E (rep U (n+2)) R) := by
  have h := E_scan_from n [] R
  simp only [List.append_nil] at h
  exact h

theorem F_one (L R : List Bool) : run0 table 1 (F (U++L) R) = some (F L (Z++R)) := by rfl

theorem F_many (n : Nat) (R : List Bool) : run0 table n (F (rep U n) R) = some (F [] (rep Z n++R)) := by
  simpa only [List.nil_append,List.append_nil,Nat.one_mul] using sweepL table 5 [] [] U Z 1 F_one n [] R

theorem E_turn (n : Nat) (R : List Bool) : run0 table 5 (E (rep U (n+2)) (true::R)) = some (F (rep U (n+1)) (false::true::R)) := by rfl

theorem E_step (k : Nat) (R : List Bool) : run0 table (2*k+8) (E [] (rep Z k++true::true::R)) = some (E [] (rep Z (k+3)++true::R)) := by
  have h1 := E_scan k (true::R)
  have h2 := E_turn k R
  have h3 := F_many (k+1) (false::true::R)
  have h4 : run0 table 1 (F [] (rep Z (k+1)++false::true::R)) = some (E [] (false::(rep Z (k+1)++false::true::R))) := by rfl
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have eq : false::(rep Z (k+1)++false::true::R) = rep Z (k+3)++true::R := by
    change Z++(rep Z (k+1)++(Z++true::R)) = _
    rw [← List.append_assoc (rep Z (k+1)) Z,rep_snoc Z (k+1)]
    rfl
  rw [eq] at H
  simpa only [show k+1+5+(k+1)+1=2*k+8 by omega] using H

def transferCost (k m : Nat) : Nat := match m with
  | 0 => 0
  | m+1 => 2*k+8+transferCost (k+3) m
termination_by m

theorem transfer (k m : Nat) : run0 table (transferCost k m) (E [] (rep Z k++rep U (m+1))) = some (E [] (rep Z (k+3*m)++[true])) := by
  induction m generalizing k with
  | zero => simp [transferCost,rep,run0]
  | succ m ih =>
    have h1 := E_step k (rep U m)
    have h2 := ih (k+3)
    have H := join0 h1 h2
    rw [show k+3+3*m=k+3*(m+1) by omega] at H
    simpa only [transferCost,rep,List.cons_append,List.nil_append] using H

theorem E_finish (k : Nat) : run0 table (k+2) (E [] (rep Z k++[true])) = some (B (k+1)) := by
  have h := E_scan k []
  have h2 : run0 table 1 (E (rep U (k+2)) []) = some (B (k+1)) := by rfl
  have H := join0 h h2
  simpa only [show k+1+1=k+2 by omega] using H

def epochCost (m : Nat) := 2+13*m+10+transferCost 3 m+(3+3*m+2)
theorem epoch (m : Nat) : run0 table (epochCost m) (B m) = some (B (3*m+4)) := by
  have h := join0 (join0 (B_start m) (D_many m)) (D_end (rep U m))
  have h2 := transfer 3 m
  have h3 := E_finish (3+3*m)
  have H := join0 (join0 h h2) h3
  rw [show 3+3*m+1=3*m+4 by omega] at H
  exact H

def count : Nat → Nat
  | 0 => 5
  | n+1 => 3*count n+4

def family (n : Nat) := B (count n)
def cost (n : Nat) := epochCost (count n)
theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := epoch (count n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 20 cost entry (by intro n; unfold cost epochCost; omega) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent11Raw107LACount
