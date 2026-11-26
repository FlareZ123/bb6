import Raw11ExtraSweepCoverage
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace Raw11ExtraFamily
open BB6Coverage
open Root56 (Side z push c right left alt10)
open Raw11ExtraSweep (alt01 alt01_add)
abbrev Config := Root56.Config

/-- The two variable ordinary rows are E1 and F0. All other rows are fixed. -/
def step (e : Bool) (f : Move) : Config → Option Config
  | (4,l,true,r) => some (right 5 l e r)
  | (5,l,false,r) => some (if f.right then right f.next.val l f.write r else left f.next.val l f.write r)
  | s => Raw11ExtraSweep.step false s

def run (e : Bool) (f : Move) : Nat → Config → Option Config
  | 0,s => some s
  | n+1,s => (step e f s).bind (run e f n)

theorem run_add (e : Bool) (f : Move) (n m : Nat) (s : Config) : run e f (n+m) s = (run e f n s).bind (run e f m) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step e f s with
    | none => rfl
    | some t => exact ih t

def sec (n : Nat) (s : Side) : Config := c 0 z false (alt10 n s)

theorem rightPair (e : Bool) (f : Move) (l r : Side) :
    run e f 6 (c 0 (false ::: l) false (alt10 1 r)) = some (c 0 (false ::: alt01 1 l) false r) := by rfl

theorem rightSweep (e : Bool) (f : Move) (n : Nat) (l r : Side) :
    run e f (6*n) (c 0 (false ::: l) false (alt10 n r)) = some (c 0 (false ::: alt01 n l) false r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 6*(n+1) = 6+6*n by omega,run_add]
    change (run e f 6 (c 0 (false ::: l) false (alt10 1 (alt10 n r)))).bind (run e f (6*n)) = _
    rw [rightPair]
    simp only [Option.bind_some]
    rw [ih,← alt01_add]

theorem leftPair (e : Bool) (f : Move) (l r : Side) :
    run e f 4 (c 0 (alt01 1 l) true (true ::: r)) = some (c 0 l true (alt10 1 (true ::: r))) := by rfl

theorem leftSweep (e : Bool) (f : Move) (n : Nat) (l r : Side) :
    run e f (4*n) (c 0 (alt01 n l) true (true ::: r)) = some (c 0 l true (alt10 n (true ::: r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 4*(n+1) = 4+4*n by omega,run_add]
    change (run e f 4 (c 0 (alt01 1 (alt01 n l)) true (true ::: r))).bind (run e f (4*n)) = _
    rw [leftPair]
    simp only [Option.bind_some]
    change run e f (4*n) (c 0 (alt01 n l) true (true ::: false ::: true ::: r)) = _
    rw [ih]
    change some (c 0 l true (alt10 n (alt10 1 (true ::: r)))) = _
    rw [← Root56.alt_add]

theorem finish (e : Bool) (f : Move) (r : Side) :
    run e f 4 (c 0 z true (true ::: r)) = some (c 0 z false (alt10 1 (true ::: r))) := by rfl

/-- Local finite turning rules lift to unbounded alternating sweeps. -/
theorem advance (e : Bool) (f : Move) (n k : Nat) (s t : Side)
    (h : ∀ l, run e f k (c 0 (false ::: false ::: true ::: l) false s) = some (c 0 l true (alt10 2 t))) :
    run e f (10*(n+1)+k) (sec (n+1) s) = some (sec (n+3) t) := by
  unfold sec
  rw [show 10*(n+1)+k = 6*(n+1)+(k+(4*n+4)) by omega,run_add]
  conv => lhs; arg 1; arg 4; rw [← Root56.zero_push]
  rw [rightSweep]
  simp only [Option.bind_some]
  rw [run_add]
  change (run e f k (c 0 (false ::: false ::: true ::: alt01 n z) false s)).bind (run e f (4*n+4)) = _
  rw [h]
  simp only [Option.bind_some]
  rw [run_add]
  change (run e f (4*n) (c 0 (alt01 n z) true (true ::: false ::: alt10 1 t))).bind (run e f 4) = _
  rw [leftSweep]
  simp only [Option.bind_some]
  change run e f 4 (c 0 z true (alt10 n (alt10 2 t))) = _
  rw [← Root56.alt_add,show n+2=1+(n+1) by omega,Root56.alt_add]
  change run e f 4 (c 0 z true (true ::: false ::: alt10 (n+1) t)) = _
  rw [finish]
  change some (c 0 z false (alt10 2 (alt10 (n+1) t))) = _
  rw [← Root56.alt_add,show 2+(n+1)=n+3 by omega]

theorem stableTurn (e : Bool) (f : Move) (l : Side) :
    run e f 29 (c 0 (false ::: false ::: true ::: l) false Raw11ExtraSweep.tail) = some (c 0 l true (alt10 2 Raw11ExtraSweep.tail)) := by rfl

theorem stableAdvance (e : Bool) (f : Move) (n : Nat) :
    run e f (10*(n+1)+29) (sec (n+1) Raw11ExtraSweep.tail) = some (sec (n+3) Raw11ExtraSweep.tail) :=
  advance e f n 29 _ _ (stableTurn e f)

/-- A positive-time growing return from an exact seed implies no finite halt. -/
theorem never_of_return (e : Bool) (f : Move) (s : Side) (n0 g N : Nat)
    (seed : run e f N Root56.blank = some (sec (n0+1) s))
    (growth : ∀ n, ∃ t, 0 < t ∧ run e f t (sec (n+1) s) = some (sec (n+g+1) s)) :
    ∀ n, run e f n Root56.blank ≠ none := by
  have long : ∀ k, ∃ t n, k ≤ t ∧ run e f t Root56.blank = some (sec (n+1) s) := by
    intro k
    induction k with
    | zero => exact ⟨N,n0,by omega,seed⟩
    | succ k ih =>
      obtain ⟨t,n,ht,hr⟩ := ih
      obtain ⟨d,hd,hs⟩ := growth n
      exact ⟨t+d,n+g,by omega,by rw [run_add,hr,Option.bind_some,hs]⟩
  intro n h
  obtain ⟨t,k,ht,hr⟩ := long n
  have hx := run_add e f n (t-n) Root56.blank
  rw [Nat.add_sub_of_le ht,hr,h] at hx
  contradiction

#print axioms advance
#print axioms never_of_return
end Raw11ExtraFamily
