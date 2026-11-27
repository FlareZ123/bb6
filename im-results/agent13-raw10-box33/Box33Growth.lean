import C9PairConjugacy

namespace BB6.Agent13.Box33Growth
open C9Pair
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def zeros : Stream := fun _ => false
@[simp] theorem zero_head : zeros 0 = false := rfl
@[simp] theorem zero_pop : pop zeros = zeros := rfl
@[simp] theorem zero_push : push false zeros = zeros := by funext n; cases n <;> rfl
def ones : Nat → Stream
  | 0 => zeros
  | n+1 => push true (ones n)
@[simp] theorem ones_succ (n : Nat) : ones (n+1) = push true (ones n) := rfl

def step (c : Config) : Option Config :=
  match c.q, c.a with
  | .A, false => some (right .B true c)
  | .B, false => some (left .C true c)
  | .C, false => some (left .A false c)
  | .C, true => some (left .D false c)
  | .D, false => some (right .D true c)
  | .D, true => some (right .C false c)
  | _, _ => none

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step c <;> simp [ih]

def phase (l r : Nat) : Config := ⟨.C,ones l,true,ones r⟩
def gap (l r : Nat) : Config := ⟨.C,push false (ones l),true,ones r⟩

theorem leftStep (l r : Nat) : run 5 (phase (l+1) r) = some (phase l (r+1)) := by
  simp [phase,run,step,left,right]

theorem leftSweep (l r : Nat) : run (5*l) (phase l r) = some (phase 0 (r+l)) := by
  induction l generalizing r with
  | zero => simp [run]
  | succ l ih =>
    rw [show 5*(l+1) = 5+5*l by omega,run_add,leftStep,Option.bind_some,ih]
    rw [show r+1+l = r+(l+1) by omega]

theorem turn (r : Nat) : run 4 (phase 0 (r+2)) = some (gap 2 r) := by
  simp [phase,gap,run,step,left,right,ones]

theorem rightStep (l r : Nat) : run 4 (gap l (r+2)) = some (gap (l+2) r) := by
  simp [gap,run,step,left,right]

theorem rightSweep (k l r : Nat) : run (4*k) (gap l (r+2*k)) = some (gap (l+2*k) r) := by
  induction k generalizing l with
  | zero => simp [run]
  | succ k ih =>
    rw [show 4*(k+1) = 4+4*k by omega,show r+2*(k+1) = (r+2*k)+2 by omega,
      run_add,rightStep,Option.bind_some,ih]
    rw [show l+2+2*k = l+2*(k+1) by omega]

theorem finish (l : Nat) : run 7 (gap l 1) = some (phase (l+2) 1) := by
  simp [phase,gap,run,step,left,right,ones]

theorem growth (k : Nat) : run (14*(k+1)+7) (phase (2*(k+1)) 1) = some (phase (2*(k+2)) 1) := by
  rw [show 14*(k+1)+7 = 5*(2*(k+1))+4+4*k+7 by omega,run_add,run_add,run_add,leftSweep,Option.bind_some]
  rw [show 1+2*(k+1) = (1+2*k)+2 by omega,turn,Option.bind_some,rightSweep,Option.bind_some,finish]
  rw [show 2+2*k+2 = 2*(k+2) by omega]

def blank : Config := ⟨.A,zeros,false,zeros⟩
theorem init : run 9 blank = some (phase 2 1) := by
  simp [blank,phase,run,step,left,right,ones]

theorem never_phase (n k : Nat) : run n (phase (2*(k+1)) 1) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    by_cases hn : n ≤ 14*(k+1)+7
    · have h' := growth k
      rw [←show n+(14*(k+1)+7-n) = 14*(k+1)+7 by omega,run_add,h] at h'
      contradiction
    · have h' := h
      rw [←show (14*(k+1)+7)+(n-(14*(k+1)+7)) = n by omega,run_add,growth,Option.bind_some] at h'
      exact ih _ (by omega) (k+1) h'

theorem never_blank (n : Nat) : run n blank ≠ none := by
  intro h
  by_cases hn : n ≤ 9
  · have h' := init
    rw [←show n+(9-n)=9 by omega,run_add,h] at h'
    contradiction
  · rw [←show 9+(n-9)=n by omega,run_add,init,Option.bind_some] at h
    exact never_phase (n-9) 0 h
#print axioms never_blank
end BB6.Agent13.Box33Growth
