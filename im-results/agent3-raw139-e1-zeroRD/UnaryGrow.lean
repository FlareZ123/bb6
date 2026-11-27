import Std
import Lean.Elab.Tactic.Omega
namespace UnaryGrow
abbrev Ray := Nat → Bool
def blank : Ray := fun _ => false
def cons (b : Bool) (r : Ray) : Ray
  | 0 => b
  | n+1 => r n
def tail (r : Ray) : Ray := fun n => r (n+1)
@[simp] theorem cz : cons false blank = blank := by funext n; cases n <;> rfl
inductive V where | rd0 | rd1 | re1 deriving DecidableEq, Repr
structure C where
  q : Fin 6
  l : Ray
  r : Ray
def table (v : V) (q : Fin 6) (b : Bool) : Option (Bool × Bool × Fin 6) :=
  match q.val,b with
  | 0,false => some (true,true,1)
  | 0,true => some (true,true,5)
  | 1,false => some (true,true,2)
  | 1,true => some (true,true,0)
  | 2,false => some (true,false,3)
  | 2,true => match v with
    | .rd0 => some (false,true,3)
    | .rd1 => some (true,true,3)
    | .re1 => some (true,true,4)
  | 3,_ => some (false,false,4)
  | 4,false => some (true,false,0)
  | 4,true => some (false,true,3)
  | 5,false => none
  | 5,true => some (false,true,2)
  | _,_ => none

def step (v : V) (c : C) : Option C :=
  (table v c.q (c.r 0)).map fun (w,d,q) =>
    if d then ⟨q,cons w c.l,tail c.r⟩
    else ⟨q,tail c.l,cons (c.l 0) (cons w (tail c.r))⟩
def run (v : V) : Nat → C → Option C
  | 0,c => some c
  | n+1,c => (step v c).bind (run v n)
theorem run_add (v : V) (n k : Nat) (c : C) :
    run v (n+k) c = (run v n c).bind (run v k) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [run]
    cases step v c with
    | none => rfl
    | some t => exact ih t

def Reach (v : V) (c d : C) : Prop := ∃ n, run v n c = some d
def Plus (v : V) (c d : C) : Prop := ∃ n, n > 0 ∧ run v n c = some d
theorem Reach.refl (v : V) (c : C) : Reach v c c := ⟨0,rfl⟩
theorem Reach.trans {v : V} {c d e : C} (h : Reach v c d) (g : Reach v d e) : Reach v c e := by
  obtain ⟨n,hn⟩ := h; obtain ⟨k,hk⟩ := g
  exact ⟨n+k, by rw [run_add,hn]; exact hk⟩
theorem Plus.reach {v : V} {c d : C} (h : Plus v c d) : Reach v c d := by
  obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
theorem Plus.thenReach {v : V} {c d e : C} (h : Plus v c d) (g : Reach v d e) : Plus v c e := by
  obtain ⟨n,hn,h⟩ := h; obtain ⟨k,hk⟩ := g
  exact ⟨n+k, by omega, by rw [run_add,h]; exact hk⟩

def ones : Nat → Ray → Ray
  | 0,r => r
  | n+1,r => cons true (ones n r)
theorem ones_add (n k : Nat) (r : Ray) : ones (n+k) r = ones n (ones k r) := by
  induction n with
  | zero => simp [ones]
  | succ n ih => rw [show n+1+k=n+k+1 by omega]; simp only [ones,ih]

def B (a : Nat) : C := ⟨1,ones a blank,blank⟩
def X (a b : Nat) : C := ⟨2,cons false (ones a blank),cons false (ones b blank)⟩
def Y (a b : Nat) : C := ⟨2,cons false (ones a blank),ones b blank⟩

theorem entry (v : V) (a : Nat) : Plus v (B (a+2)) (X (a+1) 1) := by
  cases v <;> refine ⟨8,by decide,?_⟩ <;> rfl

theorem leftOne (v : V) (a b : Nat) : Reach v (X (a+2) b) (X (a+1) (b+1)) := by
  cases v <;> exact ⟨7,rfl⟩

theorem leftSweep (v : V) (a b : Nat) : Reach v (X (a+1) b) (X 1 (a+b)) := by
  induction a generalizing b with
  | zero => simpa using Reach.refl v (X 1 b)
  | succ a ih =>
    apply Reach.trans (leftOne v a b)
    rw [show a+1+b=a+(b+1) by omega]
    exact ih (b+1)

theorem leftTurn (v : V) (b : Nat) : Reach v (X 1 (b+2)) (Y 5 b) := by
  cases v <;> refine ⟨11,?_⟩ <;> rfl

theorem rightFive (v : V) (a b : Nat) : Reach v (Y a (b+5)) (Y (a+5) b) := by
  cases v with
  | rd0 => exact ⟨9,rfl⟩
  | rd1 => exact ⟨11,rfl⟩
  | re1 => exact ⟨17,rfl⟩

theorem rightSweep (v : V) (k a b : Nat) : Reach v (Y a (5*k+b)) (Y (a+5*k) b) := by
  induction k generalizing a with
  | zero => simpa using Reach.refl v (Y a b)
  | succ k ih =>
    rw [show 5*(k+1)+b=(5*k+b)+5 by omega]
    apply Reach.trans (rightFive v a (5*k+b))
    rw [show a+5*(k+1)=(a+5)+5*k by omega]
    exact ih (a+5)

theorem y0x0 (a : Nat) : Y a 0 = X a 0 := by simp [Y,X,ones]

theorem rightExit0 (a : Nat) : Reach V.rd0 (Y a 2) (B (a+3)) := ⟨6,rfl⟩
theorem rightExit1 (a : Nat) : Reach V.rd1 (Y a 2) (B (a+3)) := ⟨8,rfl⟩
theorem rightExitE (a : Nat) : Reach V.re1 (Y a 2) (B (a+5)) := ⟨16,rfl⟩

theorem growR (v : V) (hv : v ≠ .re1) (k : Nat) : Plus v (B (5*k+8)) (B (5*(k+1)+8)) := by
  have h1 : Plus v (B (5*k+8)) (X (5*k+7) 1) := by
    simpa only [show 5*k+6+2=5*k+8 by omega,show 5*k+6+1=5*k+7 by omega] using entry v (5*k+6)
  apply Plus.thenReach h1
  have h2 : Reach v (X (5*k+7) 1) (X 1 (5*k+7)) := by
    simpa only [show 5*k+6+1=5*k+7 by omega] using leftSweep v (5*k+6) 1
  apply Reach.trans h2
  have h3 : Reach v (X 1 (5*k+7)) (Y 5 (5*(k+1))) := by
    simpa only [show 5*(k+1)+2=5*k+7 by omega] using leftTurn v (5*(k+1))
  apply Reach.trans h3
  have h4 : Reach v (Y 5 (5*(k+1))) (X (5*k+10) 0) := by
    rw [← y0x0]
    simpa only [Nat.add_zero,show 5+5*(k+1)=5*k+10 by omega] using rightSweep v (k+1) 5 0
  apply Reach.trans h4
  have h5 : Reach v (X (5*k+10) 0) (X 1 (5*k+9)) := by
    simpa only [Nat.add_zero,show 5*k+9+1=5*k+10 by omega] using leftSweep v (5*k+9) 0
  apply Reach.trans h5
  have h6 : Reach v (X 1 (5*k+9)) (Y 5 (5*(k+1)+2)) := by
    simpa only [show 5*(k+1)+2+2=5*k+9 by omega] using leftTurn v (5*(k+1)+2)
  apply Reach.trans h6
  have h7 : Reach v (Y 5 (5*(k+1)+2)) (Y (5*k+10) 2) := by
    simpa only [show 5+5*(k+1)=5*k+10 by omega] using rightSweep v (k+1) 5 2
  apply Reach.trans h7
  cases v with
  | rd0 => simpa only [show 5*k+10+3=5*(k+1)+8 by omega] using rightExit0 (5*k+10)
  | rd1 => simpa only [show 5*k+10+3=5*(k+1)+8 by omega] using rightExit1 (5*k+10)
  | re1 => exact False.elim (hv rfl)

theorem growE (k : Nat) : Plus V.re1 (B (5*k+5)) (B (5*(k+1)+5)) := by
  have h1 : Plus V.re1 (B (5*k+5)) (X (5*k+4) 1) := by
    simpa only [show 5*k+3+2=5*k+5 by omega,show 5*k+3+1=5*k+4 by omega] using entry V.re1 (5*k+3)
  apply Plus.thenReach h1
  have h2 : Reach V.re1 (X (5*k+4) 1) (X 1 (5*k+4)) := by
    simpa only [show 5*k+3+1=5*k+4 by omega] using leftSweep V.re1 (5*k+3) 1
  apply Reach.trans h2
  apply Reach.trans (leftTurn V.re1 (5*k+2))
  apply Reach.trans (rightSweep V.re1 k 5 2)
  simpa only [show 5+5*k+5=5*(k+1)+5 by omega] using rightExitE (5+5*k)

def blankC : C := ⟨0,blank,blank⟩
theorem seed0 : Reach V.rd0 blankC (B 8) := ⟨58,rfl⟩
theorem seed1 : Reach V.rd1 blankC (B 8) := ⟨60,rfl⟩
theorem seedE : Reach V.re1 blankC (B 5) := ⟨12,rfl⟩
def cfg (v : V) (k : Nat) : C := match v with
  | .re1 => B (5*k+5)
  | _ => B (5*k+8)
theorem seed (v : V) : Reach v blankC (cfg v 0) := by
  cases v with
  | rd0 => exact seed0
  | rd1 => exact seed1
  | re1 => exact seedE
theorem grow (v : V) (k : Nat) : Plus v (cfg v k) (cfg v (k+1)) := by
  cases v with
  | rd0 => exact growR .rd0 (by decide) k
  | rd1 => exact growR .rd1 (by decide) k
  | re1 => exact growE k
theorem long_prefix (v : V) (n : Nat) : ∃ k, n ≤ k ∧ run v k blankC = some (cfg v n) := by
  induction n with
  | zero => obtain ⟨k,hk⟩ := seed v; exact ⟨k,by omega,hk⟩
  | succ n ih =>
    obtain ⟨k,hk,hr⟩ := ih
    obtain ⟨j,hj,hs⟩ := grow v n
    exact ⟨k+j,by omega,by rw [run_add,hr]; exact hs⟩
theorem never (v : V) : ∀ n, ∃ c, run v n blankC = some c := by
  intro n
  obtain ⟨k,hk,hr⟩ := long_prefix v n
  cases h : run v n blankC with
  | some c => exact ⟨c,rfl⟩
  | none =>
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hk
    rw [hj,run_add,h] at hr
    contradiction
#print axioms growR
#print axioms growE
#print axioms never
end UnaryGrow
