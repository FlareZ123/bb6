import Box33D14Growth
namespace BB6.Agent13.Box33D14Growth45
open C9Pair
open Box33D14Growth (z word rep cfg ones rep_add)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def step (v : Bool) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .C false c)
  | .B,false => some (left .C true c)
  | .B,true => some (left .B true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (right .D false c)
  | .D,true => some (left .E false c)
  | .E,false => some (right .F true c)
  | .E,true => some (left .F v c)
  | .F,false => some (right .A true c)
  | .F,true => none

def run (v : Bool) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step v c).bind (run v n)

theorem run_add (v : Bool) (m n : Nat) (c : Config) : run v (m+n) c = (run v m c).bind (run v n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step v c <;> simp [ih]

abbrev blocks := rep [true,true,false]
abbrev seed := word [true,true] z
abbrev tail := word [false,true] z
abbrev L (l r : Stream) := cfg .A (word [true,true,true,true,false] l) (word [false,true] r)
abbrev R (l r : Stream) := cfg .A l r

def phase (k : Nat) : Config := cfg .A (word [true,true,false,false] (blocks (2*k+1) seed)) z

def startCost (v : Bool) : Nat := if v then 14 else 12

theorem begin (v : Bool) (k : Nat) : run v (startCost v) (phase k) = some (L (blocks (2*k) seed) tail) := by
  cases v <;> simp [startCost,phase,cfg,run,step,left,right,ones,blocks,rep,word]

theorem leftStep (v : Bool) (l r : Stream) : run v 12 (L (blocks 2 l) r) = some (L l (ones 6 r)) := by
  simp [cfg,run,step,left,right,ones,blocks,rep,word]

theorem leftSweep (v : Bool) (k : Nat) (l r : Stream) : run v (12*k) (L (blocks (2*k) l) r) = some (L l (ones (6*k) r)) := by
  induction k generalizing r with
  | zero => simp [run]
  | succ k ih =>
    rw [show 12*(k+1)=12+12*k by omega,show 2*(k+1)=2+2*k by omega,show blocks (2+2*k) l=blocks 2 (blocks (2*k) l) from rep_add _ _ _ _,run_add,leftStep,Option.bind_some,ih]
    rw [show 6*(k+1)=6*k+6 by omega,show ones (6*k+6) r=ones (6*k) (ones 6 r) from rep_add _ _ _ _]

theorem leftEnd (v : Bool) (r : Stream) : run v 12 (L seed r) = some (cfg .A seed (push false (ones 7 r))) := by
  simp [cfg,run,step,left,right,ones,rep,word]

theorem turn (v : Bool) (r : Stream) : run v 15 (cfg .A seed (push false (ones 1 r))) = some (R seed (ones 5 r)) := by
  simp [cfg,run,step,left,right,ones,rep,word]

theorem rightStep (v : Bool) (l r : Stream) : run v 7 (R l (ones 3 r)) = some (R (blocks 1 l) r) := by
  simp [cfg,run,step,left,right,ones,blocks,rep,word]

theorem rightSweep (v : Bool) (k : Nat) (l r : Stream) : run v (7*k) (R l (ones (3*k) r)) = some (R (blocks k l) r) := by
  induction k generalizing l with
  | zero => simp [run]
  | succ k ih =>
    rw [show 7*(k+1)=7+7*k by omega,show 3*(k+1)=3+3*k by omega,show ones (3+3*k) r=ones 3 (ones (3*k) r) from rep_add _ _ _ _,run_add,rightStep,Option.bind_some,ih]
    rw [show blocks (k+1) l=blocks k (blocks 1 l) from rep_add _ _ _ _]

theorem finish (v : Bool) (l : Stream) : run v 8 (R l (ones 2 tail)) = some (cfg .A (word [true,true,false,false] l) z) := by
  simp [cfg,run,step,left,right,ones,rep,word]

theorem growth (v : Bool) (k : Nat) : run v (26*k+56+startCost v) (phase k) = some (phase (k+1)) := by
  rw [show 26*k+56+startCost v=startCost v+12*k+12+15+7*(2*k+3)+8 by omega,run_add,run_add,run_add,run_add,run_add,begin,Option.bind_some,leftSweep,Option.bind_some,leftEnd,Option.bind_some]
  rw [show ones 7 (ones (6*k) tail)=ones (7+6*k) tail from (rep_add _ _ _ _).symm]
  rw [show 7+6*k=1+(6*k+6) by omega,show ones (1+(6*k+6)) tail=ones 1 (ones (6*k+6) tail) from rep_add _ _ _ _,turn,Option.bind_some]
  rw [show ones 5 (ones (6*k+6) tail)=ones (5+(6*k+6)) tail from (rep_add _ _ _ _).symm,show 5+(6*k+6)=3*(2*k+3)+2 by omega,show ones (3*(2*k+3)+2) tail=ones (3*(2*k+3)) (ones 2 tail) from rep_add _ _ _ _,rightSweep,Option.bind_some,finish]
  unfold phase
  rw [show 2*(k+1)+1=2*k+3 by omega]

def blank : Config := cfg .A z z
def initCost (v : Bool) : Nat := if v then 52 else 50

theorem init_false : run false 50 blank = some (phase 0) := by
  have h0 : run false 10 (blank) = some (cfg .C (word [true,true] z) (word [true,true] z)) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  have h1 : run false 10 (cfg .C (word [true,true] z) (word [true,true] z)) = some (cfg .A (word [true,true] z) (word [false,true,false,true] z)) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  have h2 : run false 10 (cfg .A (word [true,true] z) (word [false,true,false,true] z)) = some (cfg .D (word [] z) (word [false,false,true,true,true,true,true,true,false,true] z)) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  have h3 : run false 10 (cfg .D (word [] z) (word [false,false,true,true,true,true,true,true,false,true] z)) = some (cfg .E (word [false,true,true] z) (word [false,false,true,true,false,true] z)) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  have h4 : run false 10 (cfg .E (word [false,true,true] z) (word [false,false,true,true,false,true] z)) = some (phase 0) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  rw [show 50= 10+10+10+10+10 by omega,run_add,run_add,run_add,run_add,h0,Option.bind_some,h1,Option.bind_some,h2,Option.bind_some,h3,Option.bind_some,h4]

theorem init_true : run true 52 blank = some (phase 0) := by
  have h0 : run true 10 (blank) = some (cfg .C (word [true,true] z) (word [true,true] z)) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  have h1 : run true 10 (cfg .C (word [true,true] z) (word [true,true] z)) = some (cfg .E (word [] z) (word [false,false,false,true,false,true] z)) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  have h2 : run true 10 (cfg .E (word [] z) (word [false,false,false,true,false,true] z)) = some (cfg .B (word [true] z) (word [false,true,true,true,true,true,false,true] z)) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  have h3 : run true 10 (cfg .B (word [true] z) (word [false,true,true,true,true,true,false,true] z)) = some (cfg .D (word [false,true,true] z) (word [false,true,true,true,false,true] z)) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  have h4 : run true 10 (cfg .D (word [false,true,true] z) (word [false,true,true,true,false,true] z)) = some (cfg .E (word [false,false,true,true,false,true,true] z) (word [] z)) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  have h5 : run true 2 (cfg .E (word [false,false,true,true,false,true,true] z) (word [] z)) = some (phase 0) := by
    simp [blank,phase,cfg,run,step,left,right,ones,blocks,rep,word]
  rw [show 52= 10+10+10+10+10+2 by omega,run_add,run_add,run_add,run_add,run_add,h0,Option.bind_some,h1,Option.bind_some,h2,Option.bind_some,h3,Option.bind_some,h4,Option.bind_some,h5]

theorem init (v : Bool) : run v (initCost v) blank = some (phase 0) := by
  cases v
  · exact init_false
  · exact init_true

theorem never_phase (v : Bool) (n k : Nat) : run v n (phase k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    let m := 26*k+56+startCost v
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
end BB6.Agent13.Box33D14Growth45
