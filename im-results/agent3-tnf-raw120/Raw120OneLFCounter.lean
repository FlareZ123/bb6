import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120OneLFCounter
open BB6Coverage BB6Coverage.Agent31Pump

/-- Four raw120 1LF leaves with a shared two-counter return system.
    The only variation is A1; the common return avoids C1 forever. -/
inductive Variant where
  | ld | rd | re | lf

def table (v : Variant) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (match v with
      | .ld => ⟨false,false,3⟩ | .rd => ⟨false,true,3⟩
      | .re => ⟨false,true,4⟩ | .lf => ⟨true,false,5⟩))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def delay : Variant → Nat | .ld => 6 | .rd => 8 | .re => 6 | .lf => 4
abbrev O (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false

theorem enter (v : Variant) (R : List Bool) :
    run0 (table v) (delay v) ⟨5,[],true::true::true::R⟩ =
      some ⟨0,[false,true],true::true::true::R⟩ := by cases v <;> rfl

theorem enterRun (v : Variant) (a : Nat) (R : List Bool) :
    run0 (table v) (delay v) ⟨5,[],O (6*(a+1))++R⟩ =
      some ⟨0,[false,true],O (6*(a+1))++R⟩ := by
  rw [show 6*(a+1)=6*a+3+1+1+1 by omega]
  exact enter v (O (6*a+3)++R)

theorem pair (v : Variant) (L R : List Bool) :
    run0 (table v) 4 ⟨0,false::L,true::true::R⟩ =
      some ⟨0,false::true::true::L,R⟩ := by rfl

theorem scan (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (table v) (4*n) ⟨0,false::L,O (2*n)++R⟩ =
      some ⟨0,false::(O (2*n)++L),R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h := join0 (pair v L (O (2*n)++R)) (ih (true::true::L))
    rw [show 4*(n+1)=4+4*n by omega,show 2*(n+1)=2*n+1+1 by omega]
    simp only [List.replicate_succ, List.cons_append]
    -- The output is a homogeneous list: the two new ones may be put last.
    have he : O (2*n) ++ true::true::L = true::true::(O (2*n)++L) := by
      change O (2*n) ++ ([true,true]++L) = ([true,true]++O (2*n))++L
      rw [← List.append_assoc,show [true,true] = O 2 by rfl,
        List.replicate_append_replicate, List.replicate_append_replicate,
        Nat.add_comm (2*n) 2]
    rw [he] at h
    exact h

theorem scanStart (v : Variant) (a : Nat) (R : List Bool) :
    run0 (table v) (delay v+12*(a+1)) ⟨5,[],O (6*(a+1))++R⟩ =
      some ⟨0,false::O (6*(a+1)+1),R⟩ := by
  have h := scan v (3*(a+1)) [true] R
  rw [show 4*(3*(a+1))=12*(a+1) by omega,
    show 2*(3*(a+1))=6*(a+1) by omega,
    show [true]=O 1 by rfl,List.replicate_append_replicate] at h
  exact join0 (enterRun v a R) h

theorem growLocal (v : Variant) (L R : List Bool) :
    run0 (table v) 6 ⟨0,false::L,false::false::false::R⟩ =
      some ⟨4,true::true::true::L,true::R⟩ := by rfl

theorem eraseLocal (v : Variant) (L R : List Bool) :
    run0 (table v) 7 ⟨0,false::L,false::false::true::true::R⟩ =
      some ⟨5,true::true::L,true::true::true::R⟩ := by rfl

theorem eFinish (v : Variant) (n : Nat) (R : List Bool) :
    run0 (table v) (n+1) ⟨4,O n,R⟩ = some ⟨5,[],O (n+1)++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 ⟨4,true::O n,R⟩ = some ⟨4,O n,true::R⟩ := by rfl
    have H := join0 h (ih (true::R))
    rw [show 1+(n+1)=n+1+1 by omega] at H
    simp only [List.replicate_succ, List.cons_append]
    have he : O n ++ true::R = true::(O n++R) := by
      change O n ++ ([true]++R) = ([true]++O n)++R
      rw [← List.append_assoc,show [true]=O 1 by rfl,
        List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm n 1]
    simp only [List.replicate_succ,List.cons_append,he] at H
    exact H

theorem fErase (v : Variant) (n : Nat) (R : List Bool) :
    run0 (table v) n ⟨5,O n,R⟩ = some ⟨5,[],Z n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 ⟨5,true::O n,R⟩ = some ⟨5,O n,false::R⟩ := by rfl
    have H := join0 h (ih (false::R))
    rw [show 1+n=n+1 by omega] at H
    have he : Z n ++ false::R = false::(Z n++R) := by
      change Z n ++ ([false]++R) = ([false]++Z n)++R
      rw [← List.append_assoc,show [false]=Z 1 by rfl,
        List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm n 1]
    rw [he] at H
    exact H

theorem resetLocal (v : Variant) (R : List Bool) :
    run0 (table v) 7 ⟨5,[],false::false::false::false::R⟩ =
      some ⟨4,O 4,true::R⟩ := by rfl

theorem reset (v : Variant) (R : List Bool) :
    run0 (table v) 12 ⟨5,[],Z 4++R⟩ = some ⟨5,[],O 6++R⟩ := by
  exact join0 (resetLocal v R) (eFinish v 4 (true::R))

/-- a counts extra six-ones blocks, b counts extra three-zero blocks,
    and c counts extra ones in the last run (which always has ≥2). -/
structure Params where
  a : Nat
  b : Nat
  c : Nat

def cfg (x : Params) : Z0 := ⟨5,[],O (6*(x.a+1))++Z (3*x.b+2)++O (x.c+2)⟩
def next (x : Params) : Params :=
  match x.b with
  | 0 => ⟨0,2*x.a+1,x.c+1⟩
  | b+1 => ⟨x.a+1,b,x.c⟩
def cost (v : Variant) (x : Params) : Nat :=
  delay v + 18*(x.a+1) + (if x.b=0 then 22 else 11)

theorem advance (v : Variant) (x : Params) :
    run0 (table v) (cost v x) (cfg x) = some (cfg (next x)) := by
  rcases x with ⟨a,b,c⟩
  cases b with
  | zero =>
    have h1 := scanStart v a (Z 2++O (c+2))
    have h2 := eraseLocal v (O (6*(a+1)+1)) (O c)
    have h3 := fErase v (6*(a+1)+3) (O (c+3))
    have h4 := reset v (Z (6*a+5)++O (c+3))
    have h2' : run0 (table v) 7 ⟨0,false::O (6*(a+1)+1),Z 2++O (c+2)⟩ =
        some ⟨5,O (6*(a+1)+3),O (c+3)⟩ := by
      simpa only [List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append] using h2
    have H := join0 (join0 h1 h2') h3
    rw [show 6*(a+1)+3=4+(6*a+5) by omega] at H
    have hz : Z (4+(6*a+5)) ++ O (c+3) = Z 4 ++ (Z (6*a+5) ++ O (c+3)) := by
      simp only [Z, ← List.replicate_append_replicate, List.append_assoc]
    rw [hz] at H
    have HH := join0 H h4
    simp only [cost,cfg,next, Nat.mul_zero,Nat.zero_add, ite_true]
    rw [show 3*(2*a+1)+2=6*a+5 by omega,show c+1+2=c+3 by omega]
    rw [show delay v+18*(a+1)+22=delay v+12*(a+1)+7+(4+(6*a+5))+12 by omega]
    simpa only [List.append_assoc] using HH
  | succ b =>
    have h1 := scanStart v a (Z (3*(b+1)+2)++O (c+2))
    have h2 := growLocal v (O (6*(a+1)+1)) (Z (3*b+2)++O (c+2))
    have h2' : run0 (table v) 6 ⟨0,false::O (6*(a+1)+1),Z (3*(b+1)+2)++O (c+2)⟩ =
        some ⟨4,O (6*(a+1)+4),true::(Z (3*b+2)++O (c+2))⟩ := by
      rw [show 3*(b+1)+2=3*b+2+1+1+1 by omega]
      simpa only [List.replicate_succ,List.cons_append,show 6*(a+1)+4=6*(a+1)+1+1+1+1 by omega] using h2
    have h3 := eFinish v (6*(a+1)+4) (true::(Z (3*b+2)++O (c+2)))
    have H := join0 (join0 h1 h2') h3
    simp only [cost,cfg,next,Nat.succ_ne_zero,ite_false]
    rw [show delay v+18*(a+1)+11=delay v+12*(a+1)+6+(6*(a+1)+4+1) by omega]
    rw [show 6*(a+1+1)=6*(a+1)+4+1+1 by omega]
    have ho : O (6*(a+1)+4+1) ++ true::(Z (3*b+2)++O (c+2)) = O (6*(a+1)+4+1+1) ++ (Z (3*b+2)++O (c+2)) := by
      change O _ ++ ([true] ++ _) = _
      rw [← List.append_assoc,show [true]=O 1 by rfl,List.replicate_append_replicate]
      rfl
    rw [ho] at H
    simpa only [List.append_assoc] using H

def seed : Params := ⟨0,0,4⟩
def entryTime : Variant → Nat | .ld => 56 | .rd => 58 | .re => 56 | .lf => 54

theorem entry (v : Variant) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (cfg seed) := by
  cases v <;> rfl

def iter : Nat → Params | 0 => seed | n+1 => next (iter n)
def family (n : Nat) : Z0 := cfg (iter n)
theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (entryTime v) (fun n => cost v (iter n)) (entry v)
    (by intro n; unfold cost; split <;> omega) (fun n => advance v (iter n)) m hm
#print axioms advance
#print axioms never
end BB6.Agent3Raw120OneLFCounter
