import Box33D14Growth

namespace BB6.Agent13.Box33D17V21Pair
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def step (b : Bool) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right (if b then .B else .E) false c)
  | .B,false => some (left .C true c)
  | .B,true => if b then some (right .D false c) else none
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .C false c)
  | .E,false => some (left .F false c)
  | .E,true => if b then none else some (right .D false c)
  | .F,false => some (right .F true c)
  | .F,true => some (right .A true c)

def run (b : Bool) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step b c).bind (run b n)

theorem run_add (b : Bool) (m n : Nat) (c : Config) :
    run b (m+n) c = (run b m c).bind (run b n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step b c <;> simp [ih]

abbrev L (l r : Stream) := cfg .A l (word [false,false] r)
abbrev R (l r : Stream) := cfg .A l r

theorem lstep (b : Bool) (l r : Stream) :
    run b 5 (L (ones 1 l) r) = some (L l (ones 1 r)) := by
  cases b <;> simp [L,cfg,run,step,left,right,ones,rep,word]

theorem lsweep (b : Bool) (n : Nat) (l r : Stream) :
    run b (5*n) (L (ones n l) r) = some (L l (ones n r)) := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,
      show ones (n+1) l=ones 1 (ones n l) by rfl,run_add,lstep,Option.bind_some,ih]
    rw [show ones (n+1) r=ones n (ones 1 r) by rw [←rep_add]; congr 1; omega]

theorem turn (b : Bool) (r : Stream) :
    run b 10 (L z r) = some (R (ones 5 z) r) := by
  cases b <;> simp [L,R,cfg,run,step,left,right,ones,rep,word]

theorem rstep (b : Bool) (l r : Stream) :
    run b 11 (R l (ones 5 r)) = some (R (ones 5 l) r) := by
  cases b <;> simp [R,cfg,run,step,left,right,ones,rep,word]

theorem rsweep (b : Bool) (k : Nat) (l r : Stream) :
    run b (11*k) (R l (ones (5*k) r)) = some (R (ones (5*k) l) r) := by
  induction k generalizing l with
  | zero => simp [run]
  | succ k ih =>
    rw [show 11*(k+1)=11+11*k by omega,
      show 5*(k+1)=5+5*k by omega,
      show ones (5+5*k) r=ones 5 (ones (5*k) r) from rep_add _ _ _ _,
      run_add,rstep,Option.bind_some,ih]
    rw [show ones (5+5*k) l=ones (5*k) (ones 5 l) by
      rw [←rep_add]; congr 1; omega]

def phase (k : Nat) : Config := R (ones (5*k) z) z
theorem growth (b : Bool) (k : Nat) :
    run b (36*k+10) (phase k) = some (phase (k+1)) := by
  unfold phase
  have hz : word [false,false] z=z := by simp
  have hp : R (ones (5*k) z) z = L (ones (5*k) z) z := by unfold R L; rw [hz]
  rw [hp,show 36*k+10=5*(5*k)+10+11*k by omega,run_add,run_add,lsweep,Option.bind_some,turn,Option.bind_some,rsweep]
  rw [show 5*(k+1)=5*k+5 by omega,show ones (5*k+5) z=ones (5*k) (ones 5 z) from rep_add _ _ _ _]

def blank : Config := cfg .A z z
theorem never_phase (b : Bool) (n k : Nat) : run b n (phase k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    by_cases hn : n ≤ 36*k+10
    · have he := growth b k
      rw [←show n+(36*k+10-n)=36*k+10 by omega,run_add,h] at he
      contradiction
    · rw [←show (36*k+10)+(n-(36*k+10))=n by omega,run_add,growth,Option.bind_some] at h
      exact ih _ (by omega) (k+1) h

theorem never_blank (b : Bool) (n : Nat) : run b n blank ≠ none :=
  never_phase b n 0

#print axioms never_blank
end BB6.Agent13.Box33D17V21Pair
