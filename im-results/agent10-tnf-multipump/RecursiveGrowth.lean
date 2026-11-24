import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Recursive
open BB6Coverage BB6Coverage.Agent31Pump
namespace R69M9
-- 1RB0RB_1RC0LC_0RD0LF_1LD1RE_0LA0LB_0RA---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none
def P (n : Nat) : List Bool := rep [true,false,false] n ++ [true,true,false]
def T : Nat → Nat
  | 0 => 11
  | n+1 => 7 + T n + 3 + T n + 5
theorem first (L R : List Bool) : run0 table 7 ⟨3,[false,false,true,false,false]++L,R⟩ = some ⟨3,[false,false]++L,[true,false,true]++R⟩ := by rfl
theorem middle (L R : List Bool) : run0 table 3 ⟨4,[true,true,false]++L,[false,true]++R⟩ = some ⟨3,[false,false]++L,[false,false,true]++R⟩ := by rfl
theorem last (L R : List Bool) : run0 table 5 ⟨4,[false,true,false]++L,[false,true]++R⟩ = some ⟨4,R.headD false :: ([true,false,true,false,false]++L),R.tail⟩ := by rfl
theorem subroutine (n : Nat) (R : List Bool) :
    run0 table (T n) ⟨3,[false,false]++P n,R⟩ = some ⟨4,R.headD false :: ([true,false]++P n),R.tail⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 := first (P n) R
    have h2 := ih ([true,false,true]++R)
    have h3 := middle (P n) R
    have h4 := ih ([false,false,true]++R)
    have h5 := last (P n) R
    have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    simpa only [T,P,rep,List.append_assoc,List.cons_append,List.nil_append] using H
def family (n : Nat) : Z0 := ⟨4,[false,true,false]++P n,[]⟩
theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem start (n : Nat) : run0 table 4 (family n) = some ⟨3,[false,false]++P (n+1),[]⟩ := by rfl
theorem growth (n : Nat) : run0 table (4+T (n+1)) (family n) = some (family (n+1)) := by
  exact join0 (start n) (subroutine (n+1) [])
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 4+T (n+1)) entry (by intro n; omega) growth m hm
#print axioms never
end R69M9

namespace R69M35
-- 1RB---_1RC0LC_0RD0LF_1LD1RE_0RA0LB_1LB0RE
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none
def P (n : Nat) : List Bool := rep [true,true,false,true,false] n ++ [true,true,false,false]
def T : Nat → Nat
  | 0 => 15
  | n+1 => 9 + T n + 3 + T n + 5
theorem first (L R : List Bool) : run0 table 9 ⟨3,[false,false,true,true,false,true,false]++L,R⟩ = some ⟨3,[false,false]++L,[true,false,false,false,true]++R⟩ := by rfl
theorem middle (L R : List Bool) : run0 table 3 ⟨4,[true,true,false]++L,[false,false,false,true]++R⟩ = some ⟨3,[false,false]++L,[false,false,false,false,true]++R⟩ := by rfl
theorem last (L R : List Bool) : run0 table 5 ⟨4,[false,true,false]++L,[false,false,false,true]++R⟩ = some ⟨4,R.headD false :: ([true,false,true,true,false,true,false]++L),R.tail⟩ := by rfl
theorem subroutine (n : Nat) (R : List Bool) :
    run0 table (T n) ⟨3,[false,false]++P n,R⟩ = some ⟨4,R.headD false :: ([true,false]++P n),R.tail⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 := first (P n) R
    have h2 := ih ([true,false,false,false,true]++R)
    have h3 := middle (P n) R
    have h4 := ih ([false,false,false,false,true]++R)
    have h5 := last (P n) R
    have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    simpa only [T,P,rep,List.append_assoc,List.cons_append,List.nil_append] using H
def family (n : Nat) : Z0 := ⟨4,[false,true,false]++P n,[]⟩
theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem start (n : Nat) : run0 table 4 (family n) = some ⟨3,[false,false]++P (n+1),[]⟩ := by rfl
theorem growth (n : Nat) : run0 table (4+T (n+1)) (family n) = some (family (n+1)) := by
  exact join0 (start n) (subroutine (n+1) [])
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 (fun n => 4+T (n+1)) entry (by intro n; omega) growth m hm
#print axioms never
end R69M35

namespace R69M36
-- 1RB---_1RC0LC_0RD0LF_1LD1RE_0RA0LB_1LB1RA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none
def P (n : Nat) : List Bool := rep [true,true,false,true,false] n ++ [true,true,false,true,false,true,true,true]
def T : Nat → Nat
  | 0 => 39
  | n+1 => 9 + T n + 3 + T n + 5
theorem first (L R : List Bool) : run0 table 9 ⟨3,[false,false,true,true,false,true,false]++L,R⟩ = some ⟨3,[false,false]++L,[true,false,false,false,true]++R⟩ := by rfl
theorem middle (L R : List Bool) : run0 table 3 ⟨4,[true,true,false]++L,[false,false,false,true]++R⟩ = some ⟨3,[false,false]++L,[false,false,false,false,true]++R⟩ := by rfl
theorem last (L R : List Bool) : run0 table 5 ⟨4,[false,true,false]++L,[false,false,false,true]++R⟩ = some ⟨4,R.headD false :: ([true,false,true,true,false,true,false]++L),R.tail⟩ := by rfl
theorem subroutine (n : Nat) (R : List Bool) :
    run0 table (T n) ⟨3,[false,false]++P n,R⟩ = some ⟨4,R.headD false :: ([true,false]++P n),R.tail⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 := first (P n) R
    have h2 := ih ([true,false,false,false,true]++R)
    have h3 := middle (P n) R
    have h4 := ih ([false,false,false,false,true]++R)
    have h5 := last (P n) R
    have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    simpa only [T,P,rep,List.append_assoc,List.cons_append,List.nil_append] using H
def family (n : Nat) : Z0 := ⟨4,[false,true,false]++P n,[]⟩
theorem entry : run0 table 84 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem start (n : Nat) : run0 table 4 (family n) = some ⟨3,[false,false]++P (n+1),[]⟩ := by rfl
theorem growth (n : Nat) : run0 table (4+T (n+1)) (family n) = some (family (n+1)) := by
  exact join0 (start n) (subroutine (n+1) [])
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 84 (fun n => 4+T (n+1)) entry (by intro n; omega) growth m hm
#print axioms never
end R69M36

namespace R73M56
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none
def P (n : Nat) : List Bool := rep [false,true] n ++ [false,false,true,true]
def T : Nat → Nat
  | 0 => 13
  | n+1 => 4 + T n + 3 + T n + 2
theorem first (L R : List Bool) : run0 table 4 ⟨3,[false,true]++L,R⟩ = some ⟨3,L,[false,false]++R⟩ := by rfl
theorem middle (L R : List Bool) : run0 table 3 ⟨2,false::L,false::R⟩ = some ⟨3,L,[true,true]++R⟩ := by rfl
theorem last (L R : List Bool) : run0 table 2 ⟨2,true::L,true::R⟩ = some ⟨2,R.headD false :: ([false,true]++L),R.tail⟩ := by rfl
theorem subroutine (n : Nat) (R : List Bool) : run0 table (T n) ⟨3,P n,R⟩ = some ⟨2,R.headD false :: P n,R.tail⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 := first (P n) R
    have h2 := ih ([false,false]++R)
    have h3 := middle (P n) R
    have h4 := ih ([true,true]++R)
    have h5 := last (P n) R
    have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    simpa only [T,P,rep,List.append_assoc,List.cons_append,List.nil_append] using H
def family (n : Nat) : Z0 := ⟨2,false::P n,[]⟩
theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (3+T n+2) (family n) = some (family (n+1)) := by
  have h1 : run0 table 3 (family n) = some ⟨3,P n,[true,true]⟩ := by rfl
  have h2 := subroutine n [true,true]
  have h3 := last (P n) []
  exact join0 (join0 h1 h2) h3
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 (fun n => 3+T n+2) entry (by intro n; omega) growth m hm
#print axioms never
end R73M56
end BB6.Agent10Recursive
