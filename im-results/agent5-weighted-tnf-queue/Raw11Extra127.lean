import Root56
set_option maxRecDepth 4000
set_option maxHeartbeats 100000
namespace Raw11Extra127
open Root56

def transition (v : Fin 3) (q : Nat) (b : Bool) : Option (Bool × Bool × Fin 6) :=
  match q,b with
  | 0,false => some (true,true,1)
  | 0,true => some (true,true,3)
  | 1,false => some (true,true,2)
  | 1,true => some (false,false,4)
  | 2,false => some (false,false,0)
  | 2,true => if v=0 then some (false,true,3) else some (false,true,1)
  | 3,false => some (true,false,0)
  | 3,true => some (true,false,1)
  | 4,false => some (true,false,5)
  | 4,true => if v=0 then some (false,true,1) else some (true,false,2)
  | 5,true => if v=2 then some (false,false,3) else some (false,false,2)
  | _,_ => none

def step (v : Fin 3) : Config → Option Config
  | (q,l,b,r) => (transition v q b).map fun (w,d,q') => if d then right q'.val l w r else left q'.val l w r

def run (v : Fin 3) : Nat → Config → Option Config
  | 0,s => some s
  | n+1,s => (step v s).bind (run v n)

theorem run_add (v : Fin 3) (n m : Nat) (s : Config) : run v (n+m) s = (run v n s).bind (run v m) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step v s with
    | none => rfl
    | some t => exact ih t

def altR : Nat → Side → Side
  | 0,s => s
  | n+1,s => false ::: true ::: altR n s

def altL : Nat → Side → Side
  | 0,s => s
  | n+1,s => true ::: false ::: altL n s

theorem altR_add (n m : Nat) (s : Side) : altR (n+m) s = altR n (altR m s) := by
  induction n with
  | zero => simp only [Nat.zero_add,altR]
  | succ n ih => simp only [Nat.succ_add,altR,ih]

theorem altL_add (n m : Nat) (s : Side) : altL (n+m) s = altL n (altL m s) := by
  induction n with
  | zero => simp only [Nat.zero_add,altL]
  | succ n ih => simp only [Nat.succ_add,altL,ih]

def sec (n : Nat) : Config := c 4 z true (altR (2*n+1) z)

theorem rightSweep (v : Fin 3) (q a : Nat)
    (pair : ∀ l n, run v a (c q l true (altR (n+1) z)) = some (c q (altL 1 l) true (altR n z)))
    (n : Nat) (l : Side) : run v (a*n) (c q l true (altR n z)) = some (c q (altL n l) true z) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ,Nat.add_comm (a*n) a,run_add,pair]
    simp only [Option.bind_some]
    rw [ih,← altL_add]

theorem leftSweep (v : Fin 3) (a : Nat)
    (pair : ∀ l r, run v a (c 4 (altL 2 l) false r) = some (c 4 l false (altR 2 r)))
    (n : Nat) (l r : Side) : run v (a*n) (c 4 (altL (2*n) l) false r) = some (c 4 l false (altR (2*n) r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ,Nat.add_comm (a*n) a,run_add,show 2*(n+1)=2+2*n by omega,altL_add,pair]
    simp only [Option.bind_some]
    rw [ih,← altR_add,show 2*n+2=2+2*n by omega]

theorem right0 (l : Side) (n : Nat) : run 0 6 (c 4 l true (altR (n+1) z)) = some (c 4 (altL 1 l) true (altR n z)) := by
  cases n with
  | zero =>
    change some (c 4 (altL 1 l) true (false ::: z)) = some (c 4 (altL 1 l) true z)
    rw [zero_push]
  | succ n => rfl

theorem right1 (l : Side) (n : Nat) : run 1 2 (c 2 l true (altR (n+1) z)) = some (c 2 (altL 1 l) true (altR n z)) := by rfl

theorem right2 (l : Side) (n : Nat) : run 2 2 (c 2 l true (altR (n+1) z)) = some (c 2 (altL 1 l) true (altR n z)) := by rfl

theorem left0 (l r : Side) : run 0 8 (c 4 (altL 2 l) false r) = some (c 4 l false (altR 2 r)) := by rfl

theorem left1 (l r : Side) : run 1 8 (c 4 (altL 2 l) false r) = some (c 4 l false (altR 2 r)) := by rfl

theorem left2 (l r : Side) : run 2 6 (c 4 (altL 2 l) false r) = some (c 4 l false (altR 2 r)) := by rfl

theorem enter1 (r : Side) : run 1 4 (c 4 z true r) = some (c 2 (true ::: true ::: z) true r) := by rfl

theorem enter2 (r : Side) : run 2 4 (c 4 z true r) = some (c 2 (true ::: true ::: z) true r) := by rfl

theorem turn0 (l : Side) : run 0 8 (c 4 l true z) = some (c 4 l false (altR 1 z)) := by rfl

theorem turn1 (l : Side) : run 1 8 (c 2 l true z) = some (c 4 l false (altR 1 z)) := by rfl

theorem turn2 (l : Side) : run 2 8 (c 2 l true z) = some (c 4 l false (altR 1 z)) := by rfl

theorem finish1 (r : Side) : run 1 8 (c 4 (altL 1 (true ::: true ::: z)) false r) = some (c 4 z true (altR 2 r)) := by rfl

theorem finish2 (r : Side) : run 2 6 (c 4 (altL 1 (true ::: true ::: z)) false r) = some (c 4 z true (altR 2 r)) := by rfl

theorem finish0a (r : Side) : run 0 11 (c 4 (altL 1 z) false r) = some (c 4 z true (false ::: true ::: true ::: r)) := by rfl

theorem enter0b (r : Side) : run 0 9 (c 4 z true (false ::: true ::: true ::: altR 1 r)) = some (c 4 (true ::: true ::: z) true (altR 1 r)) := by
  change some (c 4 (true ::: true ::: false ::: z) true (altR 1 r)) = _
  rw [zero_push]

theorem finish0b (r : Side) : run 0 8 (c 4 (altL 1 (true ::: true ::: z)) false r) = some (c 4 z true (altR 2 r)) := by rfl
theorem seed0 : run 0 8 blank = some (sec 0) := by rfl
theorem seed1 : run 1 8 blank = some (sec 0) := by rfl
theorem seed2 : run 2 8 blank = some (sec 0) := by rfl
def secB (n : Nat) : Config := c 4 z true (false ::: true ::: true ::: altR (2*n+1) z)

theorem advance0a (n : Nat) : run 0 (20*n+25) (sec n) = some (secB n) := by
  unfold sec secB
  rw [show 20*n+25=6*(2*n+1)+8+8*n+11 by omega]
  rw [run_add 0 (6*(2*n+1)+8+8*n) 11,run_add 0 (6*(2*n+1)+8) (8*n),run_add 0 (6*(2*n+1)) 8]
  rw [rightSweep 0 4 6 right0 (2*n+1) z]
  simp only [Option.bind_some]
  rw [turn0]
  simp only [Option.bind_some]
  rw [altL_add (2*n) 1,leftSweep 0 8 left0]
  simp only [Option.bind_some]
  rw [finish0a,← altR_add]

theorem advance0b (n : Nat) : run 0 (20*n+31) (secB n) = some (sec (n+1)) := by
  unfold secB sec
  rw [show 20*n+31=9+6*(2*n+1)+8+8*n+8 by omega]
  rw [run_add 0 (9+6*(2*n+1)+8+8*n) 8,run_add 0 (9+6*(2*n+1)+8) (8*n),run_add 0 (9+6*(2*n+1)) 8,run_add 0 9 (6*(2*n+1))]
  rw [show altR (2*n+1) z = altR 1 (altR (2*n) z) by rw [← altR_add]; congr 1; omega,enter0b]
  simp only [Option.bind_some]
  rw [← altR_add,show 1+2*n=2*n+1 by omega,rightSweep 0 4 6 right0]
  simp only [Option.bind_some]
  rw [turn0]
  simp only [Option.bind_some]
  rw [altL_add (2*n) 1,leftSweep 0 8 left0]
  simp only [Option.bind_some]
  rw [finish0b,← altR_add,← altR_add]
  congr 3 <;> omega

theorem chain (v : Fin 3) (t u : Nat) (s x y : Config)
    (h₁ : run v t s = some x) (h₂ : run v u x = some y) : run v (t+u) s = some y := by
  rw [run_add,h₁]
  exact h₂

theorem advance0 (n : Nat) : run 0 (40*n+56) (sec n) = some (sec (n+1)) := by
  have h : 40*n+56=(20*n+25)+(20*n+31) := by omega
  exact h.symm ▸ chain 0 (20*n+25) (20*n+31) (sec n) (secB n) (sec (n+1)) (advance0a n) (advance0b n)

theorem advance1 (n : Nat) : run 1 (12*n+22) (sec n) = some (sec (n+1)) := by
  unfold sec
  rw [show 12*n+22=4+2*(2*n+1)+8+8*n+8 by omega]
  rw [run_add 1 (4+2*(2*n+1)+8+8*n) 8,run_add 1 (4+2*(2*n+1)+8) (8*n),run_add 1 (4+2*(2*n+1)) 8,run_add 1 4 (2*(2*n+1)),enter1]
  simp only [Option.bind_some]
  rw [rightSweep 1 2 2 right1]
  simp only [Option.bind_some]
  rw [turn1]
  simp only [Option.bind_some]
  rw [altL_add (2*n) 1,leftSweep 1 8 left1]
  simp only [Option.bind_some]
  rw [finish1,← altR_add,← altR_add]
  congr 3 <;> omega

theorem advance2 (n : Nat) : run 2 (10*n+20) (sec n) = some (sec (n+1)) := by
  unfold sec
  rw [show 10*n+20=4+2*(2*n+1)+8+6*n+6 by omega]
  rw [run_add 2 (4+2*(2*n+1)+8+6*n) 6,run_add 2 (4+2*(2*n+1)+8) (6*n),run_add 2 (4+2*(2*n+1)) 8,run_add 2 4 (2*(2*n+1)),enter2]
  simp only [Option.bind_some]
  rw [rightSweep 2 2 2 right2]
  simp only [Option.bind_some]
  rw [turn2]
  simp only [Option.bind_some]
  rw [altL_add (2*n) 1,leftSweep 2 6 left2]
  simp only [Option.bind_some]
  rw [finish2,← altR_add,← altR_add]
  congr 3 <;> omega

theorem never_from (v : Fin 3) (a b : Nat) (hs : run v 8 blank = some (sec 0)) (hpos : 0<b)
    (adv : ∀ n, run v (a*n+b) (sec n) = some (sec (n+1))) (k : Nat) : run v k blank ≠ none := by
  have h : ∀ n, ∃ t, n ≤ t ∧ run v t blank = some (sec n) := by
    intro n
    induction n with
    | zero => exact ⟨8,by omega,hs⟩
    | succ n ih =>
      obtain ⟨t,ht,hr⟩ := ih
      refine ⟨t+(a*n+b),by omega,?_⟩
      rw [run_add,hr]
      exact adv n
  obtain ⟨t,ht,hr⟩ := h k
  intro hn
  rw [show t=k+(t-k) by omega,run_add,hn] at hr
  contradiction

theorem never (v : Fin 3) (k : Nat) : run v k blank ≠ none := by
  have h : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases h with h|h|h
  · subst v; exact never_from 0 40 56 seed0 (by decide) advance0 k
  · subst v; exact never_from 1 12 22 seed1 (by decide) advance1 k
  · subst v; exact never_from 2 10 20 seed2 (by decide) advance2 k
#print axioms never
end Raw11Extra127
