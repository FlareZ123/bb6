import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BB6.Agent8Raw54.LA.Alternating
open BB6Coverage BB6Coverage.Agent31Pump
inductive Variant where | m48 | m55 | m56 | m69 | m70 | m122
  deriving DecidableEq, Repr

def a1 : Variant → Move
  | .m48 | .m122 => ⟨true,false,2⟩
  | .m55 | .m56 => ⟨true,false,5⟩
  | .m69 | .m70 => ⟨true,true,5⟩
def b1 : Variant → Move
  | .m122 => ⟨false,true,5⟩
  | _ => ⟨false,true,1⟩
def c1 : Variant → Move
  | .m48 => ⟨false,true,5⟩
  | _ => ⟨false,true,0⟩
def f0 : Variant → Option Transition
  | .m48 => some (some ⟨true,true,1⟩)
  | .m55 => some (some ⟨false,true,3⟩)
  | .m56 => some (some ⟨false,true,4⟩)
  | .m122 => some (some ⟨true,true,2⟩)
  | _ => none
def f1 : Variant → Option Transition
  | .m69 => some (some ⟨true,false,3⟩)
  | .m70 => some (some ⟨true,false,4⟩)
  | _ => none

def table (v : Variant) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (a1 v))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some (b1 v))
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (c1 v))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => f0 v
  | 5,true => f1 v
  | _,_ => none

def pair : List Bool := [false,true]
def quad : List Bool := [false,true,false,true]
def mark : List Bool := [false,false,true,true]
def family (n : Nat) : Z0 := ⟨3,mark ++ rep quad n,[]⟩

theorem quadEq (n : Nat) : rep pair (2*n) = rep quad n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    simp only [rep,ih]
    rfl

theorem leftDrain (v : Variant) (k : Nat) (R : List Bool) :
    run0 (table v) (4*k+1) ⟨4,rep pair k,R⟩ =
      some ⟨0,[],true::(rep pair k++R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => cases v <;> rfl
    | succ k =>
      have h : run0 (table v) 4 ⟨4,rep pair (k+2),R⟩ =
          some ⟨4,rep pair (k+1),pair++R⟩ := by cases v <;> rfl
      have g := join0 h (ih (pair++R))
      rw [show 4+(4*(k+1)+1)=4*(k+2)+1 by omega] at g
      have e : rep pair (k+1) ++ (pair++R) = rep pair (k+2)++R := by
        rw [← List.append_assoc,rep_snoc]
        rfl
      rw [e] at g
      exact g

theorem drainQuad (v : Variant) (n : Nat) (R : List Bool) :
    run0 (table v) (8*n+1) ⟨4,rep quad n,R⟩ =
      some ⟨0,[],true::(rep quad n++R)⟩ := by
  have h := leftDrain v (2*n) R
  rw [quadEq,show 4*(2*n)+1=8*n+1 by omega] at h
  exact h

theorem rightDrain (v : Variant) (n : Nat) (R : List Bool) :
    run0 (table v) (4*n) ⟨1,[true,true],rep quad n++R⟩ =
      some ⟨1,[true,true]++rep quad n,R⟩ := by
  simpa only [List.append_nil,List.nil_append] using
    sweepR (table v) 1 [true,true] [] quad quad 4 (by intro L R; cases v <;> rfl) n [] R

theorem epoch (v : Variant) (n : Nat) :
    run0 (table v) (24*n+30) (family n) = some (family (n+2)) := by
  have h0 : run0 (table v) 4 (family n) = some ⟨4,rep quad n,mark⟩ := by rfl
  have h1 := drainQuad v n mark
  have h2 : run0 (table v) 1 ⟨0,[],true::(rep quad n++mark)⟩ =
    some ⟨1,[true,true],rep quad n++mark⟩ := by rfl
  have h3 := rightDrain v n mark
  have h4 : run0 (table v) 4 ⟨1,[true,true]++rep quad n,mark⟩ =
    some ⟨4,rep quad (n+1),pair⟩ := by cases v <;> rfl
  have h5 := drainQuad v (n+1) pair
  have h6 : run0 (table v) 1 ⟨0,[],true::(rep quad (n+1)++pair)⟩ =
    some ⟨1,[true,true],rep quad (n+1)++pair⟩ := by rfl
  have h7 := rightDrain v (n+1) pair
  have h8 : run0 (table v) 6 ⟨1,[true,true]++rep quad (n+1),pair⟩ =
    some (family (n+2)) := by cases v <;> rfl
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4) h5) h6) h7) h8
  rw [show 4+(8*n+1)+1+4*n+4+(8*(n+1)+1)+1+4*(n+1)+6=24*n+30 by omega] at H
  exact H

def orbit (n : Nat) : Z0 := family (2*n)
theorem entry (v : Variant) : run0 (table v) 3 ⟨0,[],[]⟩ = some (orbit 0) := by rfl
theorem growth (v : Variant) (n : Nat) :
    run0 (table v) (24*(2*n)+30) (orbit n) = some (orbit (n+1)) := by
  have H := epoch v (2*n)
  rw [show 2*n+2=2*(n+1) by omega] at H
  exact H
theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) orbit 3 (fun n => 24*(2*n)+30) (entry v) (by intro n; omega) (growth v) m hm
#print axioms epoch
#print axioms never
end BB6.Agent8Raw54.LA.Alternating
