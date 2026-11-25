import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LB0LC42
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LB_1RC0LC_0RD1LE_1LD1RA_0RD0RF_---0RE
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def U : List Bool := [true]
def Z : List Bool := [false]
def family (n : Nat) : Z0 := ⟨4,[false],[true,false,false]++rep U (2*n+3)⟩
theorem entry : run0 table 25 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem start (R : List Bool) : run0 table 5 ⟨4,[false],[true,false,false,true]++R⟩ = some ⟨4,[true,true,true,false],[true]++R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 2 ⟨4,[true]++L,[true,true]++R⟩ = some ⟨4,[true,false,false]++L,R⟩ := by rfl

theorem turn (L : List Bool) :
    run0 table 3 ⟨4,[true]++L,[true]⟩ = some ⟨3,[false,false,false,false]++L,[]⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 1 ⟨3,[false]++L,R⟩ = some ⟨3,L,[true]++R⟩ := by rfl

theorem finish (R : List Bool) :
    run0 table 4 ⟨3,[true,true,false],[true,true,true]++R⟩ =
      some ⟨4,[false],[true,false,false,true,true]++R⟩ := by rfl

private theorem rep_add (p : List Bool) (n m : Nat) : rep p (n+m) = rep p n ++ rep p m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=(n+m)+1 by omega,rep,ih]; simp only [rep,List.append_assoc]
private theorem rep_pair (b : Bool) (n : Nat) : rep [b,b] n = rep [b] (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2*n+2 by omega]
    rfl

theorem growth (n : Nat) : run0 table (4*n+20) (family n) = some (family (n+1)) := by
  have h1 := start (rep U (2*n+2))
  have h1' : run0 table 5 (family n) = some ⟨4,[true,true,true,false],rep U (2*n+3)⟩ := h1
  have h2 := sweepR table 4 [true] [] [true,true] [false,false] 2 rightOne (n+1) [true,true,false] [true]
  simp only [List.nil_append,rep_pair] at h2
  have eq : rep [true] (2*(n+1))++[true] = rep U (2*n+3) := by
    change rep U (2*(n+1))++rep U 1 = _
    rw [← rep_add]; congr 1
  rw [eq] at h2
  have h3 := turn (rep [false] (2*(n+1))++[true,true,false])
  have h3' : run0 table 3 ⟨4,[true]++rep [false] (2*(n+1))++[true,true,false],[true]⟩ =
      some ⟨3,rep Z (2*n+6)++[true,true,false],[]⟩ := by
    rw [show 2*n+6=2*(n+1)+4 by omega]
    exact h3
  have h4 := sweepL table 3 [] [] Z U 1 leftOne (2*n+6) [true,true,false] []
  simp only [List.append_nil,List.nil_append,Nat.one_mul] at h4
  have h5 := finish (rep U (2*n+3))
  have h5' : run0 table 4 ⟨3,[true,true,false],rep U (2*n+6)⟩ = some (family (n+1)) := by
    unfold family
    rw [show 2*(n+1)+3=2*n+5 by omega]
    exact h5
  have H := join0 (join0 (join0 (join0 h1' h2) h3') h4) h5'
  rw [show 5+2*(n+1)+3+(2*n+6)+4=4*n+20 by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 25 (fun n => 4*n+20) entry (by omega) growth m hm
#print axioms never
end BB6.Agent47Raw41.LB0LC42
