import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw107LECountdown
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
abbrev U := [true]
abbrev Z := [false,false,false]
abbrev z := [false]
abbrev Q := [false,true,false]
abbrev D (n : Nat) (R : List Bool) : Z0 := ⟨3,[false,false]++rep U (3*n+1)++Q,R⟩
abbrev A (n : Nat) (R : List Bool) : Z0 := ⟨0,[false]++rep U (3*n+2)++Q,R⟩

theorem enter (n : Nat) (R : List Bool) : run0 table 6 (D n R) = some ⟨5,rep U (3*n+1)++Q,[true,false]++R⟩ := by rfl

theorem F_one (L R : List Bool) : run0 table 1 ⟨5,U++L,R⟩ = some ⟨5,L,z++R⟩ := by rfl

theorem F_many (n : Nat) (R : List Bool) : run0 table n ⟨5,rep U n++Q,R⟩ = some ⟨5,Q,rep z n++R⟩ := by
  simpa only [List.nil_append,Nat.one_mul] using sweepL table 5 [] [] U z 1 F_one n Q R

theorem zeros_triple (n : Nat) : rep z (3*n) = rep Z n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 3*(n+1)=3*n+1+1+1 by omega]; simp only [rep,ih]; rfl

theorem pre (n : Nat) (R : List Bool) : run0 table (3*n+13) (D (n+1) R) = some (D 0 (rep Z n++Q++R)) := by
  have h := join0 (enter (n+1) R) (F_many (3*(n+1)+1) ([true,false]++R))
  have h2 : run0 table 3 ⟨5,Q,rep z (3*(n+1)+1)++([true,false]++R)⟩ = some (D 0 (rep Z n++Q++R)) := by
    rw [show 3*(n+1)+1=3*n+1+1+1+1 by omega]
    simp only [rep,List.append_assoc]
    rw [zeros_triple]
    have h3 : run0 table 3 ⟨5,Q,z++(z++(z++(z++(rep Z n++([true,false]++R)))))⟩ = some (D 0 (z++(rep Z n++([true,false]++R)))) := by rfl
    rw [h3]
    have e : z++rep Z n = rep Z n++z := by
      rw [← zeros_triple n,rep_snoc z (3*n)]
    rw [← List.append_assoc z (rep Z n),e]
    rw [List.append_assoc]
    rfl
  have H := join0 h h2
  simpa only [show 6+(3*(n+1)+1)+3=3*n+13 by omega] using H

theorem afterZeros (n : Nat) (R : List Bool) : run0 table 3 (A n (Z++R)) = some (D (n+1) R) := by
  unfold A D
  rw [show 3*(n+1)+1=3*n+2+1+1 by omega]
  rfl

theorem afterEnd (n : Nat) (R : List Bool) : run0 table 3 (A n (Q++R)) = some (A (n+1) R) := by
  unfold A
  rw [show 3*(n+1)+2=3*n+2+1+1+1 by omega]
  rfl

def C : Nat → Nat
  | 0 => 10
  | n+1 => 2*C n+6

def advanceCost : Nat → Nat
  | 0 => 0
  | n+1 => advanceCost n+C n+3

theorem costRel (n : Nat) : advanceCost n+3*n+10 = C n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advanceCost,C]; omega

theorem advance (n : Nat) (R : List Bool) (h : ∀ k, k<n → ∀ S : List Bool, run0 table (C k) (D k S) = some (A k S)) : run0 table (advanceCost n) (D 0 (rep Z n++R)) = some (D n R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 := ih (Z++R) (fun k hk => h k (by omega))
    have h2 := h n (by omega) (Z++R)
    have H := join0 (join0 h1 h2) (afterZeros n R)
    rw [← List.append_assoc,rep_snoc Z n] at H
    exact H

theorem clear (n : Nat) (R : List Bool) : run0 table (C n) (D n R) = some (A n R) := by
  induction n using Nat.strongRecOn generalizing R with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have h1 := pre n R
      have h2 := advance n (Q++R) (fun k hk => ih k (by omega))
      have h3 := ih n (by omega) (Q++R)
      rw [← List.append_assoc] at h2
      have H := join0 (join0 (join0 h1 h2) h3) (afterEnd n R)
      have rel := costRel n
      simpa only [C,show (3*n+13)+advanceCost n+C n+3=2*C n+6 by omega] using H

def family (n : Nat) := D (n+1) []
def cost (n : Nat) := C (n+1)+3

theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem endBlank (n : Nat) : run0 table 3 (A n []) = some (D (n+1) []) := by
  unfold A D
  rw [show 3*(n+1)+1=3*n+2+1+1 by omega]
  rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  exact join0 (clear (n+1) []) (endBlank (n+1))

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 23 cost entry (by intro n; unfold cost; omega) growth m hm
#print axioms entry
#print axioms growth
#print axioms never
end BB6.Agent11Raw107LECountdown
