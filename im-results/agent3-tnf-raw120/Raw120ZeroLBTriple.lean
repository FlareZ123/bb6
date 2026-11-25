import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120ZeroLBTriple
open BB6Coverage BB6Coverage.Agent31Pump

/-- Leaves 732 (false) and 978 (true) share the same recursive shuttle;
    the leftward control states differ. -/
def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => if v then none else some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,if v then 5 else 0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,false,if v then 0 else 1⟩)
  | 5,true => if v then some (some ⟨true,false,1⟩) else none
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true
abbrev S (R : List Bool) := false::true::true::R

def T : Nat → Nat | 0 => 13 | n+1 => 2*T n+15
def ret (v : Bool) : Fin 6 := if v then 5 else 0

theorem core (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (T n) ⟨2,true::L,O (3*n)++S R⟩ =
      some ⟨ret v,L,O (3*n+1)++S R⟩ := by
  induction n generalizing L with
  | zero => cases v <;> rfl
  | succ n ih =>
    rw [show 3*(n+1)=3*n+1+1+1 by omega]
    simp only [List.replicate_succ,List.cons_append]
    have h1 : run0 (table v) 3 ⟨2,true::L,true::true::true::(O (3*n)++S R)⟩ =
        some ⟨2,true::false::false::false::L,O (3*n)++S R⟩ := by rfl
    have h2 := ih (false::false::false::L)
    have h3 : run0 (table v) 7 ⟨ret v,false::false::false::L,true::(O (3*n)++S R)⟩ =
        some ⟨2,true::false::false::true::L,O (3*n)++S R⟩ := by cases v <;> rfl
    have h4 := ih (false::false::true::L)
    have h5 : run0 (table v) 5 ⟨ret v,false::false::true::L,true::(O (3*n)++S R)⟩ =
        some ⟨ret v,L,true::true::true::true::(O (3*n)++S R)⟩ := by cases v <;> rfl
    have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    rw [show 3+T n+7+T n+5=T (n+1) by simp [T]; omega] at h
    exact h

theorem extra (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (T n+6) ⟨2,true::L,O (3*n+2)++S R⟩ =
      some ⟨1,L,O (3*n+3)++S R⟩ := by
  have h1 : run0 (table v) 2 ⟨2,true::L,true::true::(O (3*n)++S R)⟩ =
      some ⟨2,true::false::false::L,O (3*n)++S R⟩ := by rfl
  have h2 := core v n (false::false::L) R
  have h3 : run0 (table v) 4 ⟨ret v,false::false::L,true::(O (3*n)++S R)⟩ =
      some ⟨1,L,true::true::true::(O (3*n)++S R)⟩ := by cases v <;> rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 2+T n+4=T n+6 by omega] at h
  exact h

def family (n : Nat) : Z0 := ⟨1,[],O (3*n+3)++S [true,true]⟩

theorem entry (v : Bool) : run0 (table v) 21 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem step (v : Bool) (n : Nat) :
    run0 (table v) (T n+12) (family n) = some (family (n+1)) := by
  have h1 : run0 (table v) 1 (family n) =
      some ⟨2,[true,true],O (3*n+2)++S [true,true]⟩ := by rfl
  have h2 := extra v n [true] [true,true]
  have h3 : run0 (table v) 5 ⟨1,[true],O (3*n+3)++S [true,true]⟩ =
      some ⟨1,[],true::true::true::(O (3*n+3)++S [true,true])⟩ := by cases v <;> rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 1+(T n+6)+5=T n+12 by omega] at h
  unfold family
  rw [show 3*(n+1)+3=3*n+3+1+1+1 by omega]
  exact h

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 21 (fun n => T n+12) (entry v) (by intro n; omega) (step v) m hm
#print axioms never
end BB6.Agent3Raw120ZeroLBTriple
