import Box33D14Growth
namespace BB6.Agent13.Box33D14Growth1
open C9Pair
open Box33D14Growth (z word rep cfg ones rep_add)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,true => some (right .D false c)
  | .B,true => some (right .F true c)
  | .E,true => some (left .D true c)
  | _,_ => Box33D14Growth.step c

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step c <;> simp [ih]

abbrev pairs := rep [false,true]
abbrev seed := word [false,true,true,true] z
abbrev tail := word [false,false,true] z
abbrev E (l r : Stream) := cfg .E l (push true r)
abbrev A (l r : Stream) := cfg .A l (word [false,true,false,false,true] r)

def phase (k : Nat) : Config := cfg .A (ones (6*k+3) seed) z

theorem begin (k : Nat) : run 4 (phase k) = some (E (ones (6*k+1) seed) tail) := by
  unfold phase
  rw [show 6*k+3=2+(6*k+1) by omega,show ones (2+(6*k+1)) seed=ones 2 (ones (6*k+1) seed) from rep_add _ _ _ _]
  simp [cfg,run,step,Box33D14Growth.step,left,right,ones,rep,word]

theorem leftStep (l r : Stream) : run 2 (E (ones 2 l) r) = some (E l (pairs 1 r)) := by
  simp [cfg,run,step,Box33D14Growth.step,left,right,ones,pairs,rep,word]

theorem leftSweep (k : Nat) (l r : Stream) : run (2*k) (E (ones (2*k) l) r) = some (E l (pairs k r)) := by
  induction k generalizing r with
  | zero => simp [run]
  | succ k ih =>
    rw [show 2*(k+1)=2+2*k by omega,show ones (2+2*k) l=ones 2 (ones (2*k) l) from rep_add _ _ _ _,run_add,leftStep,Option.bind_some,ih]
    rw [show pairs (k+1) r=pairs k (pairs 1 r) from rep_add _ _ _ _]

theorem leftEnd (r : Stream) : run 2 (E (ones 1 seed) r) = some (cfg .E (ones 3 z) (word [false,false,true] r)) := by
  simp [cfg,run,step,Box33D14Growth.step,left,right,ones,rep,word]

theorem turn (r : Stream) : run 28 (cfg .E (ones 3 z) (word [false,false,true] r)) = some (A seed r) := by
  have h0 : run 10 (cfg .E (ones 3 z) (word [false,false,true] r)) = some (cfg .A z (word [false,true,false,false,false,false,true] r)) := by
    simp [cfg,run,step,Box33D14Growth.step,left,right,ones,rep,word]
  have h1 : run 10 (cfg .A z (word [false,true,false,false,false,false,true] r)) = some (cfg .A z (word [false,true,false,true,false,false,true,false,true] r)) := by
    simp [cfg,run,step,Box33D14Growth.step,left,right,ones,rep,word]
  have h2 : run 8 (cfg .A z (word [false,true,false,true,false,false,true,false,true] r)) = some (A seed r) := by
    simp [cfg,run,step,Box33D14Growth.step,left,right,ones,rep,word]
  rw [show 28=10+10+8 by omega,run_add,run_add,h0,Option.bind_some,h1,Option.bind_some,h2]

theorem rightStep (l r : Stream) : run 10 (A l (pairs 3 r)) = some (A (ones 6 l) r) := by
  simp [cfg,run,step,Box33D14Growth.step,left,right,ones,pairs,rep,word]

theorem rightSweep (k : Nat) (l r : Stream) : run (10*k) (A l (pairs (3*k) r)) = some (A (ones (6*k) l) r) := by
  induction k generalizing l with
  | zero => simp [run]
  | succ k ih =>
    rw [show 10*(k+1)=10+10*k by omega,show 3*(k+1)=3+3*k by omega,show pairs (3+3*k) r=pairs 3 (pairs (3*k) r) from rep_add _ _ _ _,run_add,rightStep,Option.bind_some,ih]
    rw [show 6*(k+1)=6*k+6 by omega,show ones (6*k+6) l=ones (6*k) (ones 6 l) from rep_add _ _ _ _]

theorem finish (l : Stream) : run 9 (A l tail) = some (cfg .A (ones 9 l) z) := by
  simp [cfg,run,step,Box33D14Growth.step,left,right,ones,rep,word]

theorem growth (k : Nat) : run (16*k+43) (phase k) = some (phase (k+1)) := by
  rw [show 16*k+43=4+2*(3*k)+2+28+10*k+9 by omega,run_add,run_add,run_add,run_add,run_add,begin,Option.bind_some]
  rw [show 6*k+1=2*(3*k)+1 by omega,show ones (2*(3*k)+1) seed=ones (2*(3*k)) (ones 1 seed) from rep_add _ _ _ _,leftSweep,Option.bind_some,leftEnd,Option.bind_some,turn,Option.bind_some,rightSweep,Option.bind_some,finish]
  unfold phase
  rw [show ones 9 (ones (6*k) seed)=ones (9+6*k) seed from (rep_add _ _ _ _).symm,show 9+6*k=6*(k+1)+3 by omega]

def blank : Config := cfg .A z z

theorem init : run 28 blank = some (phase 0) := by
  have h0 : run 10 (blank) = some (cfg .A (word [true,true,true] z) (word [] z)) := by
    simp [blank,phase,cfg,run,step,Box33D14Growth.step,left,right,ones,rep,word]
  have h1 : run 10 (cfg .A (word [true,true,true] z) (word [] z)) = some (cfg .A (word [true,true,true] z) (word [true,false,false,true] z)) := by
    simp [blank,phase,cfg,run,step,Box33D14Growth.step,left,right,ones,rep,word]
  have h2 : run 8 (cfg .A (word [true,true,true] z) (word [true,false,false,true] z)) = some (phase 0) := by
    simp [blank,phase,cfg,run,step,Box33D14Growth.step,left,right,ones,rep,word]
  rw [show 28=10+10+8 by omega,run_add,run_add,h0,Option.bind_some,h1,Option.bind_some,h2]

theorem never_phase (n k : Nat) : run n (phase k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    by_cases hn : n≤16*k+43
    · have he := growth k; rw [←show n+(16*k+43-n)=16*k+43 by omega,run_add,h] at he; contradiction
    · rw [←show (16*k+43)+(n-(16*k+43))=n by omega,run_add,growth,Option.bind_some] at h
      exact ih _ (by omega) (k+1) h

theorem never_blank (n : Nat) : run n blank ≠ none := by
  intro h
  by_cases hn : n≤28
  · have he := init; rw [←show n+(28-n)=28 by omega,run_add,h] at he; contradiction
  · rw [←show 28+(n-28)=n by omega,run_add,init,Option.bind_some] at h
    exact never_phase _ 0 h
#print axioms never_blank
end BB6.Agent13.Box33D14Growth1
