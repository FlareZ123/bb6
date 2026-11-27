import Box33D14Growth

namespace BB6.Agent13.Box33D17V21Unary
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .C false c)
  | .B,false => some (left .C true c)
  | .B,true => none
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .E false c)
  | .E,false => some (left .F false c)
  | .E,true => some (left .F true c)
  | .F,false => some (right .F true c)
  | .F,true => some (right .A false c)

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step c <;> simp [ih]

abbrev zeros := rep [false]
abbrev L (l r : Stream) := cfg .A l (push true r)
abbrev F (l r : Stream) := cfg .F l r

def phase (k : Nat) : Config := cfg .A (push false (ones (5*k+4) z)) z

theorem start (l : Stream) :
    run 8 (cfg .A (push false (ones 3 l)) z) =
      some (L l (zeros 4 (push true z))) := by
  simp [L,cfg,run,step,left,right,ones,zeros,rep,word]

theorem lstep (l r : Stream) :
    run 7 (L (ones 5 l) r) = some (L l (zeros 5 r)) := by
  simp [L,cfg,run,step,left,right,ones,zeros,rep,word]

theorem lsweep (k : Nat) (l r : Stream) :
    run (7*k) (L (ones (5*k) l) r) = some (L l (zeros (5*k) r)) := by
  induction k generalizing r with
  | zero => simp [run]
  | succ k ih =>
    rw [show 7*(k+1)=7+7*k by omega,
      show 5*(k+1)=5+5*k by omega,
      show ones (5+5*k) l=ones 5 (ones (5*k) l) from rep_add _ _ _ _,
      run_add,lstep,Option.bind_some,ih]
    rw [show zeros (5+5*k) r=zeros (5*k) (zeros 5 r) by
      rw [←rep_add]; congr 1; omega]

theorem turn (r : Stream) :
    run 4 (L (ones 1 z) r) = some (F z (zeros 5 r)) := by
  simp [L,F,cfg,run,step,left,right,ones,zeros,rep,word]

theorem rstep (l r : Stream) :
    run 1 (F l (zeros 1 r)) = some (F (ones 1 l) r) := by
  simp [F,cfg,run,step,left,right,ones,zeros,rep,word]

theorem rsweep (n : Nat) (l r : Stream) :
    run n (F l (zeros n r)) = some (F (ones n l) r) := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1=1+n by omega,show zeros (1+n) r=zeros 1 (zeros n r) from rep_add _ _ _ _,
      run_add,rstep,Option.bind_some,ih]
    rw [show ones (1+n) l=ones n (ones 1 l) by rw [←rep_add]; congr 1; omega]

theorem finish (l : Stream) :
    run 1 (F l (push true z)) = some (cfg .A (push false l) z) := by
  simp [F,cfg,run,step,left,right]

theorem growth (k : Nat) :
    run (12*k+22) (phase k) = some (phase (k+1)) := by
  unfold phase
  rw [show 5*k+4=3+(5*k+1) by omega,
      show ones (3+(5*k+1)) z=ones 3 (ones (5*k+1) z) from rep_add _ _ _ _,
      show 12*k+22=8+7*k+4+(5*k+9)+1 by omega,
      run_add,run_add,run_add,run_add,start,Option.bind_some]
  rw [show ones (5*k+1) z=ones (5*k) (ones 1 z) from rep_add _ _ _ _,
      lsweep,Option.bind_some,turn,Option.bind_some]
  rw [←rep_add,←rep_add,show 5+5*k+4=5*k+9 by omega,rsweep,Option.bind_some,finish]
  rw [show 5*(k+1)+4=5*k+9 by omega]

def blank : Config := cfg .A z z
theorem init : run 10 blank = some (phase 0) := by
  simp [blank,phase,cfg,run,step,left,right,ones,rep,word]

theorem never_phase (n k : Nat) : run n (phase k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    by_cases hn : n ≤ 12*k+22
    · have he := growth k
      rw [←show n+(12*k+22-n)=12*k+22 by omega,run_add,h] at he
      contradiction
    · rw [←show (12*k+22)+(n-(12*k+22))=n by omega,run_add,growth,Option.bind_some] at h
      exact ih _ (by omega) (k+1) h

theorem never_blank (n : Nat) : run n blank ≠ none := by
  intro h
  by_cases hn : n≤10
  · have he := init; rw [←show n+(10-n)=10 by omega,run_add,h] at he; contradiction
  · rw [←show 10+(n-10)=n by omega,run_add,init,Option.bind_some] at h
    exact never_phase _ 0 h

#print axioms never_blank
end BB6.Agent13.Box33D17V21Unary
