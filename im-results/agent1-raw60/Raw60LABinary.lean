import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LABinary
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev U (k : Nat) := List.replicate k true
abbrev Z (k : Nat) := List.replicate k false
abbrev Q : List Bool := [false,true,true,true,true]
abbrev J : List Bool := [true,true,true,true]

theorem clearC (k : Nat) (L R : List Bool) :
    run0 table (k+1) (C (true::L) (U k ++ false::R)) =
      some (C (false::(Z (k+1) ++ L)) R) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h1 : run0 table 1 (C (true::L) (U (k+1) ++ false::R)) =
        some (C (true::false::L) (U k ++ false::R)) := by rfl
    have H := join0 h1 (ih (false::L))
    rw [show 1+(k+1)=k+1+1 by omega] at H
    simpa only [List.replicate_succ' (n:=k+1) (a:=false),List.append_assoc,List.singleton_append] using H

theorem prepare (k : Nat) (L R : List Bool) :
    run0 table (k+1) (B (false::L) (U k ++ Q ++ R)) =
      some (C (false::(Z k ++ true::L)) (J++R)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 1 (B (false::L) (U (k+1) ++ Q ++ R)) =
        some (C (true::true::L) (U k ++ false::(J++R))) := by
      simp only [List.append_assoc]; rfl
    have H := join0 h1 (clearC k (true::L) (J++R))
    rw [show 1+(k+1)=k+1+1 by omega] at H
    exact H

theorem reset (L R : List Bool) :
    run0 table 9 (C (false::L) (J++R)) = some (B L (Q++R)) := by rfl

theorem flip (k : Nat) (L R : List Bool) :
    run0 table (k+10) (B (false::L) (U k ++ Q ++ R)) =
      some (B (Z k ++ true::L) (Q++R)) := by
  have H := join0 (prepare k L R) (reset (Z k ++ true::L) R)
  rw [show k+1+9=k+10 by omega] at H
  exact H

theorem emit (L R : List Bool) :
    run0 table 2 (B (true::false::L) (Q++R)) = some (B L (true::true::(Q++R))) := by rfl

def T : Nat → Nat
  | 0 => 0
  | n+1 => 2*T n + 2*n + 12

theorem traverse (n : Nat) (L R : List Bool) :
    run0 table (T n) (B (Z (2*n) ++ L) (Q++R)) =
      some (B L (U (2*n) ++ Q ++ R)) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 := ih (false::false::L)
    have h2 := flip (2*n) (false::L) R
    have h3 := ih (true::false::L)
    have h4 : run0 table 2 (B (true::false::L) (U (2*n) ++ Q ++ R)) =
        some (B L (true::true::(U (2*n) ++ Q ++ R))) := by rfl
    have H := join0 (join0 (join0 h1 h2) h3) h4
    rw [show T n + (2*n+10) + T n + 2 = T (n+1) by simp only [T]; omega] at H
    have ha : Z (2*(n+1)) ++ L = Z (2*n) ++ false::false::L := by
      change List.replicate (2*(n+1)) false ++ L = List.replicate (2*n) false ++ false::false::L
      rw [show 2*(n+1)=2*n+2 by omega,← List.replicate_append_replicate,List.append_assoc]
      rfl
    have hb : U (2*(n+1)) ++ Q ++ R = true::true::(U (2*n) ++ Q ++ R) := by
      rw [show 2*(n+1)=2*n+1+1 by omega]
      rfl
    rw [ha,hb]
    exact H

def family (n : Nat) : Z0 := B [] (U (2*n) ++ Q)
def cost (n : Nat) := 2*n+10+T n+2

theorem init (k : Nat) (R : List Bool) :
    run0 table (k+10) (B [] (U k ++ Q ++ R)) =
      some (B (Z k ++ [true]) (Q++R)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 1 (B [] (U (k+1) ++ Q ++ R)) =
        some (C [true,true] (U k ++ false::(J++R))) := by
      simp only [List.append_assoc]; rfl
    have H := join0 (join0 h1 (clearC k [true] (J++R))) (reset (Z (k+1) ++ [true]) R)
    rw [show 1+(k+1)+9=k+1+10 by omega] at H
    exact H

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := init (2*n) []
  have h2 := traverse n [true] []
  have h3 : run0 table 2 (B [true] (U (2*n) ++ Q)) = some (B [] (true::true::(U (2*n) ++ Q))) := by rfl
  simp only [List.append_nil] at h1 h2
  have H := join0 (join0 h1 h2) h3
  unfold family cost
  rw [show 2*(n+1)=2*n+1+1 by omega]
  exact H

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (n : Nat) : 0 < cost n := by unfold cost; omega
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 cost entry positive growth m hm
#print axioms traverse
#print axioms growth
#print axioms never
end BB6.Agent1Raw60LABinary
