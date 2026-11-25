import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LBFour
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev U (n : Nat) := List.replicate n true

theorem repU (n : Nat) : rep [true] n = U n := by induction n <;> simp [rep,List.replicate_succ, *]
theorem uAdd (a b : Nat) : U a ++ U b = U (a+b) := List.replicate_append_replicate

theorem clearOne (L R : List Bool) : run0 table 1 (C (true::L) R) = some (C L (true::R)) := by rfl

theorem clear (k : Nat) (L R : List Bool) :
    run0 table (k+1) (F (true::(U k++L)) R) = some (C L (U k++false::R)) := by
  have h1 : run0 table 1 (F (true::(U k++L)) R) = some (C (U k++L) (false::R)) := by rfl
  have h2 := sweepL table 2 [] [] [true] [true] 1 clearOne k L (false::R)
  simp only [List.nil_append,Nat.one_mul,repU] at h2
  have H := join0 h1 h2
  rw [Nat.add_comm 1 k] at H
  exact H

def P (n : Nat) := 5*n+4

def gCost : Nat → Nat
  | 0 => 13
  | n+1 => 2*(2*gCost n+P n+1)+P n+14

def tCost (n : Nat) := P n+1+gCost n
def hCost (n : Nat) := gCost n+tCost n

def G (n : Nat) : Prop := ∀ L R : List Bool,
  run0 table (gCost n) (C (false::L) (U (P n)++false::R)) = some (F (false::(U (P n)++false::L)) R)

def H (n : Nat) : Prop := ∀ L R : List Bool,
  run0 table (hCost n) (C (false::L) (U (P n+1)++R)) = some (F (false::(U (P n)++false::L)) R)

theorem traverseOfG (n : Nat) (h : G n) (L R : List Bool) :
    run0 table (tCost n) (F (true::(U (P n)++false::L)) R) = some (F (false::(U (P n)++false::L)) R) :=
  join0 (clear (P n) (false::L) R) (h L R)

theorem gBase : G 0 := by intro L R; rfl

theorem hBase : H 0 := by intro L R; rfl

theorem push4 (L R : List Bool) :
    run0 table 5 (F (false::L) (U 4++R)) = some (F (U 4++L) (true::R)) := by rfl

theorem finish (b : Bool) (L R : List Bool) :
    run0 table 5 (F (false::L) ([true,true,false,true,b]++R)) = some (F (b::(U 5++L)) R) := by cases b <;> rfl

theorem advance (n : Nat) (ih : H n) (b : Bool) (L R : List Bool) :
    run0 table (gCost (n+1)) (C (false::L) (U (P (n+1))++b::R)) =
      some (F (b::(U (P (n+1))++false::L)) R) := by
  have h1 := ih L (U 4++b::R)
  have h2 := push4 (U (P n)++false::L) (b::R)
  have h3 := clear (P n+3) (false::L) (true::b::R)
  have hp : P (n+1)=P n+5 := by simp [P]; omega
  have hu : U 4++(U (P n)++false::L) = true::(U (P n+3)++false::L) := by
    rw [← List.append_assoc,uAdd,show 4+P n=P n+3+1 by omega]; rfl
  rw [hu] at h2
  have h4 := ih L (U 2++false::true::b::R)
  have hv : U (P n+1)++(U 2++false::true::b::R) = U (P n+3)++false::true::b::R := by
    rw [← List.append_assoc,uAdd,show P n+1+2=P n+3 by omega]
  rw [hv] at h4
  have h5 := finish b (U (P n)++false::L) R
  have hh : U (P n+1)++(U 4++b::R) = U (P (n+1))++b::R := by
    rw [← List.append_assoc,uAdd,hp,show P n+1+4=P n+5 by omega]
  rw [hh] at h1
  have he : U 5++(U (P n)++false::L) = U (P (n+1))++false::L := by
    rw [← List.append_assoc,uAdd,hp,Nat.add_comm 5]
  rw [he] at h5
  have J := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show hCost n+5+(P n+3+1)+hCost n+5=gCost (n+1) by simp only [hCost,tCost,gCost]; omega] at J
  exact J

theorem both (n : Nat) : G n ∧ H n := by
  induction n with
  | zero => exact ⟨gBase,hBase⟩
  | succ n ih =>
    have g : G (n+1) := fun L R => advance n ih.2 false L R
    have h : H (n+1) := by
      intro L R
      have h1 := advance n ih.2 true L R
      have hh : U (P (n+1))++true::R = U (P (n+1)+1)++R := by
        rw [show U (P (n+1)+1)=U (P (n+1))++[true] by exact List.replicate_succ',List.append_assoc]; rfl
      rw [hh] at h1
      exact join0 h1 (traverseOfG (n+1) g L R)
    exact ⟨g,h⟩

theorem traverse (n : Nat) (L R : List Bool) :
    run0 table (tCost n) (F (true::(U (P n)++false::L)) R) = some (F (false::(U (P n)++false::L)) R) := traverseOfG n (both n).1 L R

theorem turn (L : List Bool) :
    run0 table 13 (F (false::(U 1++L)) []) = some (F (U 7++L) []) := by rfl

def family (n : Nat) := F (true::(U (P (n+1))++[false])) []
def cost (n : Nat) := tCost (n+1)+13

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := traverse (n+1) [] []
  have h2 := turn (U (P (n+1)-1)++[false])
  have h : U 1++(U (P (n+1)-1)++[false])=U (P (n+1))++[false] := by
    rw [← List.append_assoc,uAdd,show 1+(P (n+1)-1)=P (n+1) by simp [P]; omega]
  rw [h] at h2
  have h' : U 7++(U (P (n+1)-1)++[false])=true::(U (P (n+2))++[false]) := by
    rw [← List.append_assoc,uAdd,show 7+(P (n+1)-1)=P (n+2)+1 by simp [P]; omega]; rfl
  rw [h'] at h2
  exact join0 h1 h2

theorem entry : run0 table 83 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (n : Nat) : 0 < cost n := by unfold cost; omega
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never_of_growth table family 83 cost entry positive growth m hm
#print axioms both
#print axioms traverse
#print axioms never
end BB6.Agent1Raw60LBFour
