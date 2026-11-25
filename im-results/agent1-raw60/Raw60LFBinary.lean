import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LFBinary
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev U (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false
abbrev Q : List Bool := [false,true,false,true]
abbrev J : List Bool := [true,false,true]

theorem clearB (k : Nat) (L R : List Bool) :
    run0 table (k+1) (B (true::L) (U k++Q++R)) =
      some (B (false::(Z (k+1)++L)) (J++R)) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h1 : run0 table 1 (B (true::L) (U (k+1)++Q++R)) =
        some (B (true::false::L) (U k++Q++R)) := by rfl
    have H := join0 h1 (ih (false::L))
    rw [show 1+(k+1)=k+1+1 by omega] at H
    simpa only [List.replicate_succ' (n:=k+1) (a:=false),List.append_assoc,List.singleton_append] using H

theorem reset (L R : List Bool) :
    run0 table 9 (B (false::L) (J++R)) = some (A L (Q++R)) := by rfl

theorem flip (k : Nat) (L R : List Bool) :
    run0 table (k+10) (A (false::L) (U k++Q++R)) =
      some (A (Z k++true::L) (Q++R)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 1 (A (false::L) (U (k+1)++Q++R)) =
        some (B (true::true::L) (U k++Q++R)) := by rfl
    have H := join0 (join0 h1 (clearB k (true::L) R)) (reset (Z (k+1)++true::L) R)
    rw [show 1+(k+1)+9=k+1+10 by omega] at H
    exact H

def T : Nat → Nat
  | 0 => 0
  | n+1 => 2*T n+2*n+12

theorem traverse (n : Nat) (L R : List Bool) :
    run0 table (T n) (A (Z (2*n)++L) (Q++R)) =
      some (A L (U (2*n)++Q++R)) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 := ih (false::false::L)
    have h2 := flip (2*n) (false::L) R
    have h3 := ih (true::false::L)
    have h4 : run0 table 2 (A (true::false::L) (U (2*n)++Q++R)) =
        some (A L (true::true::(U (2*n)++Q++R))) := by rfl
    have H := join0 (join0 (join0 h1 h2) h3) h4
    rw [show T n+(2*n+10)+T n+2=T (n+1) by simp only [T]; omega] at H
    have ha : Z (2*(n+1))++L = Z (2*n)++false::false::L := by
      change List.replicate (2*(n+1)) false ++ L = List.replicate (2*n) false ++ false::false::L
      rw [show 2*(n+1)=2*n+2 by omega,← List.replicate_append_replicate,List.append_assoc]
      rfl
    have hb : U (2*(n+1))++Q++R = true::true::(U (2*n)++Q++R) := by
      rw [show 2*(n+1)=2*n+1+1 by omega]
      rfl
    rw [ha,hb]
    exact H

def family (n : Nat) : Z0 := A [] (U (2*n)++Q)
def cost (n : Nat) := 2*n+10+T n+2

theorem init (k : Nat) (R : List Bool) :
    run0 table (k+10) (A [] (U k++Q++R)) = some (A (Z k++[true]) (Q++R)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 1 (A [] (U (k+1)++Q++R)) =
        some (B [true,true] (U k++Q++R)) := by rfl
    have H := join0 (join0 h1 (clearB k [true] R)) (reset (Z (k+1)++[true]) R)
    rw [show 1+(k+1)+9=k+1+10 by omega] at H
    exact H

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := init (2*n) []
  have h2 := traverse n [true] []
  have h3 : run0 table 2 (A [true] (U (2*n)++Q)) = some (A [] (true::true::(U (2*n)++Q))) := by rfl
  simp only [List.append_nil] at h1 h2
  have H := join0 (join0 h1 h2) h3
  unfold family cost
  rw [show 2*(n+1)=2*n+1+1 by omega]
  exact H

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (n : Nat) : 0 < cost n := by unfold cost; omega
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11 cost entry positive growth m hm
#print axioms never
#print axioms traverse
#print axioms growth
#print axioms entry
end BB6.Agent1Raw60LFBinary
