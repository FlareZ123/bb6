import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120OneLFTwo
open BB6Coverage BB6Coverage.Agent31Pump

/-- Raw120 1LF leaf 2549; the return avoids B1 forever. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false

theorem enter (R : List Bool) :
    run0 table 17 ⟨5,[],true::true::true::true::true::true::R⟩ =
      some ⟨0,[false,true,true,true],false::true::true::true::true::R⟩ := by rfl

theorem pair (L R : List Bool) :
    run0 table 4 ⟨0,false::L,false::true::true::R⟩ =
      some ⟨0,false::true::true::L,false::R⟩ := by rfl

theorem scan (n : Nat) (L R : List Bool) :
    run0 table (4*n) ⟨0,false::L,false::(O (2*n)++R)⟩ =
      some ⟨0,false::(O (2*n)++L),false::R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h := join0 (pair L (O (2*n)++R)) (ih (true::true::L))
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

theorem scanStart (a : Nat) (R : List Bool) :
    run0 table (17+4*(3*a+2)) ⟨5,[],O (6*(a+1))++R⟩ =
      some ⟨0,false::O (6*(a+1)+1),false::R⟩ := by
  have h := scan (3*a+2) [true,true,true] R
  rw [show 2*(3*a+2)=6*a+4 by omega,
    show [true,true,true]=O 3 by rfl,List.replicate_append_replicate,
    show 6*a+4+3=6*(a+1)+1 by omega] at h
  have e := enter (O (6*a)++R)
  have ee : run0 table 17 ⟨5,[],O (6*(a+1))++R⟩ =
      some ⟨0,[false,true,true,true],false::(O (6*a+4)++R)⟩ := by
    rw [show 6*(a+1)=6*a+1+1+1+1+1+1 by omega,
        show 6*a+4=6*a+1+1+1+1 by omega]
    exact e
  exact join0 ee h

theorem growLocal (L R : List Bool) :
    run0 table 7 ⟨0,false::L,false::false::false::R⟩ =
      some ⟨4,true::true::L,true::true::R⟩ := by rfl

theorem eraseLocal (L R : List Bool) :
    run0 table 7 ⟨0,false::L,false::false::true::true::R⟩ =
      some ⟨5,true::true::L,true::true::true::R⟩ := by rfl

theorem eFinish (n : Nat) (R : List Bool) :
    run0 table (n+1) ⟨4,O n,R⟩ = some ⟨5,[],O (n+1)++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 ⟨4,true::O n,R⟩ = some ⟨4,O n,true::R⟩ := by rfl
    have H := join0 h (ih (true::R))
    rw [show 1+(n+1)=n+1+1 by omega] at H
    simp only [List.replicate_succ, List.cons_append]
    have he : O n ++ true::R = true::(O n++R) := by
      change O n ++ ([true]++R) = ([true]++O n)++R
      rw [← List.append_assoc,show [true]=O 1 by rfl,
        List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm n 1]
    simp only [List.replicate_succ,List.cons_append,he] at H
    exact H

theorem fErase (n : Nat) (R : List Bool) :
    run0 table n ⟨5,O n,R⟩ = some ⟨5,[],Z n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 ⟨5,true::O n,R⟩ = some ⟨5,O n,false::R⟩ := by rfl
    have H := join0 h (ih (false::R))
    rw [show 1+n=n+1 by omega] at H
    have he : Z n ++ false::R = false::(Z n++R) := by
      change Z n ++ ([false]++R) = ([false]++Z n)++R
      rw [← List.append_assoc,show [false]=Z 1 by rfl,
        List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm n 1]
    rw [he] at H
    exact H

theorem resetLocal (R : List Bool) :
    run0 table 7 ⟨5,[],false::false::false::false::R⟩ =
      some ⟨4,O 4,true::R⟩ := by rfl

theorem reset (R : List Bool) :
    run0 table 12 ⟨5,[],Z 4++R⟩ = some ⟨5,[],O 6++R⟩ := by
  exact join0 (resetLocal R) (eFinish 4 (true::R))

structure Params where
  a : Nat
  b : Nat
  c : Nat

def cfg (x : Params) : Z0 := ⟨5,[],O (6*(x.a+1))++Z (2*x.b+1)++O (x.c+2)⟩
def next (x : Params) : Params :=
  match x.b with
  | 0 => ⟨0,3*x.a+2,x.c+1⟩
  | b+1 => ⟨x.a+1,b,x.c⟩
def cost (x : Params) : Nat := 18*(x.a+1) + (if x.b=0 then 35 else 24)

theorem advance (x : Params) : run0 table (cost x) (cfg x) = some (cfg (next x)) := by
  rcases x with ⟨a,b,c⟩
  cases b with
  | zero =>
    have h1 := scanStart a (Z 1++O (c+2))
    have h2 := eraseLocal (O (6*(a+1)+1)) (O c)
    have h3 := fErase (6*(a+1)+3) (O (c+3))
    have h4 := reset (Z (6*a+5)++O (c+3))
    have h2' : run0 table 7 ⟨0,false::O (6*(a+1)+1),false::(Z 1++O (c+2))⟩ =
        some ⟨5,O (6*(a+1)+3),O (c+3)⟩ := by rfl
    have H := join0 (join0 h1 h2') h3
    rw [show 6*(a+1)+3=4+(6*a+5) by omega] at H
    have hz : Z (4+(6*a+5)) ++ O (c+3) = Z 4 ++ (Z (6*a+5) ++ O (c+3)) := by
      simp only [Z, ← List.replicate_append_replicate, List.append_assoc]
    rw [hz] at H
    have HH := join0 H h4
    simp only [cost,cfg,next,Nat.mul_zero,Nat.zero_add,ite_true]
    rw [show 2*(3*a+2)+1=6*a+5 by omega,show c+1+2=c+3 by omega,
      show 18*(a+1)+35=17+4*(3*a+2)+7+(4+(6*a+5))+12 by omega]
    simpa only [List.append_assoc] using HH
  | succ b =>
    have h1 := scanStart a (Z (2*(b+1)+1)++O (c+2))
    have h2 := growLocal (O (6*(a+1)+1)) (Z (2*b+1)++O (c+2))
    have h2' : run0 table 7 ⟨0,false::O (6*(a+1)+1),false::(Z (2*(b+1)+1)++O (c+2))⟩ =
        some ⟨4,O (6*(a+1)+3),true::true::(Z (2*b+1)++O (c+2))⟩ := by
      rw [show 2*(b+1)+1=2*b+1+1+1 by omega]
      exact h2
    have h3 := eFinish (6*(a+1)+3) (true::true::(Z (2*b+1)++O (c+2)))
    have H := join0 (join0 h1 h2') h3
    simp only [cost,cfg,next,Nat.succ_ne_zero,ite_false]
    rw [show 18*(a+1)+24=17+4*(3*a+2)+7+(6*(a+1)+3+1) by omega,
      show 6*(a+1+1)=6*(a+1)+3+1+2 by omega]
    have ho : O (6*(a+1)+3+1) ++ true::true::(Z (2*b+1)++O (c+2)) = O (6*(a+1)+3+1+2) ++ (Z (2*b+1)++O (c+2)) := by
      change O _ ++ ([true,true] ++ _) = _
      rw [← List.append_assoc,show [true,true]=O 2 by rfl,List.replicate_append_replicate]
      rfl
    rw [ho] at H
    simpa only [List.append_assoc] using H

def seed : Params := ⟨0,1,3⟩
theorem entry : run0 table 63 ⟨0,[],[]⟩ = some (cfg seed) := by rfl
def iter : Nat → Params | 0 => seed | n+1 => next (iter n)
def family (n : Nat) : Z0 := cfg (iter n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 63 (fun n => cost (iter n)) entry
    (by intro n; unfold cost; split <;> omega) (fun n => advance (iter n)) m hm
#print axioms advance
#print axioms never
end BB6.Agent3Raw120OneLFTwo
