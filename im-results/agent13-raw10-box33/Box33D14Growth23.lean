import Box33D14Growth
namespace BB6.Agent13.Box33D14Growth23
open C9Pair
open Box33D14Growth (z word rep cfg ones blocks C A rep_add)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def step (v : Bool) (c : Config) : Option Config :=
  match c.q,c.a with
  | .E,false => some (right (if v then .F else .C) true c)
  | _,_ => Box33D14Growth.step c

def run (v : Bool) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step v c).bind (run v n)

theorem run_add (v : Bool) (m n : Nat) (c : Config) : run v (m+n) c = (run v m c).bind (run v n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step v c <;> simp [ih]

theorem begin (v : Bool) (l : Stream) : run v 2 (cfg .A l z) = some (C l z) := by
  simp [cfg,run,step,Box33D14Growth.step,left,right]

theorem leftStep (v : Bool) (l r : Stream) : run v 3 (C (ones 3 l) r) = some (C l (blocks 1 r)) := by
  simp [cfg,run,step,Box33D14Growth.step,left,right,ones,blocks,rep]

theorem leftSweep (v : Bool) (n : Nat) (l r : Stream) : run v (3*n) (C (ones (3*n) l) r) = some (C l (blocks n r)) := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,show ones (3+3*n) l=ones 3 (ones (3*n) l) from rep_add _ _ _ _,run_add,leftStep,Option.bind_some,ih]
    rw [show blocks (n+1) r=blocks n (blocks 1 r) from rep_add _ _ _ _]

theorem turn (v : Bool) (r : Stream) : run v 4 (C (ones 2 z) r) = some (cfg .A z (blocks 2 r)) := by
  simp [cfg,run,step,Box33D14Growth.step,left,right,ones,blocks,rep]

def overhead (v : Bool) : Nat := if v then 10 else 12

theorem startRight (v : Bool) (r : Stream) : run v (overhead v) (cfg .A z (blocks 2 r)) = some (A (ones 4 z) r) := by
  cases v <;> simp [overhead,cfg,run,step,Box33D14Growth.step,left,right,ones,blocks,rep]

theorem rightStep (v : Bool) (l r : Stream) : run v 10 (A l (blocks 2 r)) = some (A (ones 6 l) r) := by
  simp [cfg,run,step,Box33D14Growth.step,left,right,ones,blocks,rep]

theorem rightSweep (v : Bool) (n : Nat) (l r : Stream) : run v (10*n) (A l (blocks (2*n) r)) = some (A (ones (6*n) l) r) := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    rw [show 10*(n+1)=10+10*n by omega,show 2*(n+1)=2+2*n by omega,show blocks (2+2*n) r=blocks 2 (blocks (2*n) r) from rep_add _ _ _ _,run_add,rightStep,Option.bind_some,ih]
    rw [show 6*(n+1)=6*n+6 by omega,show ones (6*n+6) l=ones (6*n) (ones 6 l) from rep_add _ _ _ _]

theorem finish (v : Bool) (l : Stream) : run v 8 (A l z) = some (cfg .A (ones 4 l) z) := by
  simp [cfg,run,step,Box33D14Growth.step,left,right,ones,blocks,rep]

def phase (k : Nat) : Config := cfg .A (ones (6*k+2) z) z

theorem growth (v : Bool) (k : Nat) : run v (16*k+14+overhead v) (phase k) = some (phase (k+1)) := by
  unfold phase
  rw [show 16*k+14+overhead v=2+3*(2*k)+4+overhead v+10*k+8 by omega,run_add,run_add,run_add,run_add,run_add,begin,Option.bind_some]
  rw [show 6*k+2=3*(2*k)+2 by omega,show ones (3*(2*k)+2) z=ones (3*(2*k)) (ones 2 z) from rep_add _ _ _ _,leftSweep,Option.bind_some,turn,Option.bind_some,startRight,Option.bind_some,rightSweep,Option.bind_some,finish]
  rw [show ones (6*k) (ones 4 z)=ones (6*k+4) z from (rep_add _ _ _ _).symm,show 6*(k+1)+2=4+(6*k+4) by omega,show ones (4+(6*k+4)) z=ones 4 (ones (6*k+4) z) from rep_add _ _ _ _]

def blank : Config := cfg .A z z
def initCost (v : Bool) : Nat := if v then 8 else 10

theorem init (v : Bool) : run v (initCost v) blank = some (phase 0) := by
  cases v <;> simp [initCost,blank,phase,cfg,run,step,Box33D14Growth.step,left,right,ones,rep]

theorem never_phase (v : Bool) (n k : Nat) : run v n (phase k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    let m := 16*k+14+overhead v
    have hp : 0<m := by dsimp [m]; omega
    by_cases hn : n≤m
    · have he := growth v k; change run v m (phase k)=_ at he; rw [←show n+(m-n)=m by omega,run_add,h] at he; contradiction
    · rw [←show m+(n-m)=n by omega,run_add,show run v m (phase k)=_ from growth v k,Option.bind_some] at h
      exact ih _ (by omega) (k+1) h

theorem never_blank (v : Bool) (n : Nat) : run v n blank ≠ none := by
  intro h
  by_cases hn : n≤initCost v
  · have he := init v; rw [←show n+(initCost v-n)=initCost v by omega,run_add,h] at he; contradiction
  · rw [←show initCost v+(n-initCost v)=n by omega,run_add,init,Option.bind_some] at h
    exact never_phase v _ 0 h
#print axioms never_blank
end BB6.Agent13.Box33D14Growth23
