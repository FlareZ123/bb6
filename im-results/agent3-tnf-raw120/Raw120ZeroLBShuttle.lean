import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120ZeroLBShuttle
open BB6Coverage BB6Coverage.Agent31Pump

/-- 0LB leaves 920 and 921; only F1 differs. -/
def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,if v then 5 else 1⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true
abbrev S (R : List Bool) := false::true::true::R

def T : Nat → Nat | 0 => 13 | n+1 => 2*T n+7

/-- Recursive shuttle, arbitrary left and right tails. Each pair of extra
    ones causes two traversals of the smaller shuttle. -/
theorem core (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (T n) ⟨2,true::L,O (2*n)++S R⟩ =
      some ⟨5,L,O (2*n+1)++S R⟩ := by
  induction n generalizing L with
  | zero => cases v <;> rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    simp only [List.replicate_succ,List.cons_append]
    have h1 : run0 (table v) 2 ⟨2,true::L,true::true::(O (2*n)++S R)⟩ =
        some ⟨2,true::false::false::L,O (2*n)++S R⟩ := by rfl
    have h2 := ih (false::false::L)
    have h3 : run0 (table v) 3 ⟨5,false::false::L,true::(O (2*n)++S R)⟩ =
        some ⟨2,true::true::true::L,O (2*n)++S R⟩ := by rfl
    have h4 := ih (true::true::L)
    have h5 : run0 (table v) 2 ⟨5,true::true::L,true::(O (2*n)++S R)⟩ =
        some ⟨5,L,true::true::true::(O (2*n)++S R)⟩ := by cases v <;> rfl
    have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    rw [show 2+T n+3+T n+2=T (n+1) by simp [T]; omega] at h
    exact h

def family (n : Nat) : Z0 := ⟨5,[],O (2*n+1)++S [true,true]⟩

theorem entry (v : Bool) : run0 (table v) 17 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem step (v : Bool) (n : Nat) :
    run0 (table v) (T n+5) (family n) = some (family (n+1)) := by
  have h1 : run0 (table v) 3 (family n) =
      some ⟨2,[true,true,true],O (2*n)++S [true,true]⟩ := by rfl
  have h2 := core v n [true,true] [true,true]
  have h3 : run0 (table v) 2 ⟨5,[true,true],O (2*n+1)++S [true,true]⟩ =
      some ⟨5,[],true::true::(O (2*n+1)++S [true,true])⟩ := by cases v <;> rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 3+T n+2=T n+5 by omega] at h
  unfold family
  rw [show 2*(n+1)+1=2*n+1+1+1 by omega]
  exact h

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 17 (fun n => T n+5) (entry v) (by intro n; omega) (step v) m hm
#print axioms never
end BB6.Agent3Raw120ZeroLBShuttle
