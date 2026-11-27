import Box33D14Growth
namespace BB6.Agent13.Box33D14V18Growth
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .C false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (right .D false c)
  | .D,true => some (right .E false c)
  | .E,false => some (left .B true c)
  | .E,true => some (left .A true c)
  | .F,false => none
  | .F,true => some (right .A true c)

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step c <;> simp [ih]

abbrev blocks := rep [false,false,true,true,true]
abbrev R (l r : Stream) := cfg .A (ones 3 l) r
abbrev phase (n : Nat) := cfg .A z (word [false,false] (ones n z))
abbrev L (l r : Stream) := R l (word [false,false] r)

theorem start (r : Stream) : run 10 (cfg .A z (word [false,false,true,true] r)) = some (R z r) := by
  simp [cfg,run,step,left,right,ones,rep,word]

theorem rstep (l r : Stream) : run 9 (R l (ones 5 r)) = some (R (blocks 1 l) r) := by
  simp [cfg,run,step,left,right,ones,blocks,rep,word]

theorem lstep (l r : Stream) : run 11 (L (blocks 1 l) r) = some (L l (ones 5 r)) := by
  simp [cfg,run,step,left,right,ones,blocks,rep,word]

theorem lend (r : Stream) : run 11 (L z r) = some (cfg .A z (word [false,false] (ones 5 r))) := by
  simp [cfg,run,step,left,right,ones,blocks,rep,word]

theorem turn (l : Stream) : run 8 (R l (ones 3 z)) = some (L l (ones 2 z)) := by
  simp [cfg,run,step,left,right,ones,blocks,rep,word]

theorem rsweep (k : Nat) (l r : Stream) : run (9*k) (R l (ones (5*k) r)) = some (R (blocks k l) r) := by
  induction k generalizing l with
  | zero => simp [run]
  | succ k ih =>
    rw [show 9*(k+1)=9+9*k by omega,show 5*(k+1)=5+5*k by omega,show ones (5+5*k) r=ones 5 (ones (5*k) r) from rep_add _ _ _ _,run_add,rstep,Option.bind_some,ih]
    rw [show blocks (k+1) l=blocks k (blocks 1 l) from rep_add _ _ _ _]

theorem lsweep (k : Nat) (l r : Stream) : run (11*k) (L (blocks k l) r) = some (L l (ones (5*k) r)) := by
  induction k generalizing r with
  | zero => simp [run]
  | succ k ih =>
    rw [show 11*(k+1)=11+11*k by omega,show blocks (k+1) l=blocks 1 (blocks k l) by rfl,run_add,lstep,Option.bind_some,ih]
    rw [show 5*(k+1)=5*k+5 by omega,show ones (5*k+5) r=ones (5*k) (ones 5 r) from rep_add _ _ _ _]

theorem finish (k : Nat) (r : Stream) : run (11*(k+1)) (L (blocks k z) r) = some (cfg .A z (word [false,false] (ones (5*(k+1)) r))) := by
  rw [show 11*(k+1)=11*k+11 by omega,run_add,lsweep,Option.bind_some,lend]
  rw [show 5*(k+1)=5+5*k by omega,show ones (5+5*k) r=ones 5 (ones (5*k) r) from rep_add _ _ _ _]

theorem phaseA (k : Nat) : run (20*k+29) (phase (5*k+5)) = some (phase (5*k+7)) := by
  rw [show 5*k+5=2+(5*k+3) by omega,show 20*k+29=10+9*k+8+11*(k+1) by omega,run_add,run_add,run_add]
  rw [show phase (2+(5*k+3))=cfg .A z (word [false,false,true,true] (ones (5*k+3) z)) by unfold phase; rw [show ones (2+(5*k+3)) z=ones 2 (ones (5*k+3) z) from rep_add _ _ _ _]; rfl,start,Option.bind_some]
  rw [show ones (5*k+3) z=ones (5*k) (ones 3 z) from rep_add _ _ _ _,rsweep,Option.bind_some,turn,Option.bind_some,finish]
  unfold phase; rw [show 5*k+7=5*(k+1)+2 by omega,show ones (5*(k+1)+2) z=ones (5*(k+1)) (ones 2 z) from rep_add _ _ _ _]

theorem phaseB (k : Nat) : run (20*k+41) (phase (5*k+7)) = some (phase (5*(k+1)+5)) := by
  rw [show 5*k+7=2+5*(k+1) by omega,show 20*k+41=10+9*(k+1)+11*(k+2) by omega,run_add,run_add]
  rw [show phase (2+5*(k+1))=cfg .A z (word [false,false,true,true] (ones (5*(k+1)) z)) by unfold phase; rw [show ones (2+5*(k+1)) z=ones 2 (ones (5*(k+1)) z) from rep_add _ _ _ _]; rfl,start,Option.bind_some,rsweep,Option.bind_some]
  have hz : word [false,false] z=z := by simp
  rw [show R (blocks (k+1) z) z=L (blocks (k+1) z) z by unfold L; rw [hz]]
  rw [show k+2=(k+1)+1 by omega,finish]
  simp only [phase]
  congr 2

def blank : Config := cfg .A z z

theorem init : run 30 blank = some (phase 5) := by
  have h1 : run 9 blank = some (phase 2) := by simp [blank,cfg,run,step,left,right,ones,rep,word]
  have h2 : run 10 (phase 2) = some (R z z) := start z
  have h3 : run 11 (R z z) = some (phase 5) := by
    have hz : word [false,false] z=z := by simp
    rw [show R z z=L z z by unfold L; rw [hz]]
    exact lend z
  rw [show 30=9+10+11 by decide,run_add,run_add,h1,Option.bind_some,h2,Option.bind_some,h3]

theorem progress (k : Nat) : run (40*k+70) (phase (5*k+5)) = some (phase (5*(k+1)+5)) := by
  rw [show 40*k+70=(20*k+29)+(20*k+41) by omega,run_add,phaseA,Option.bind_some,phaseB]

theorem never_phase (n k : Nat) : run n (phase (5*k+5)) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    let m := 40*k+70
    have hp : 0<m := by dsimp [m]; omega
    by_cases hn : n≤m
    · have he := progress k; change run m (phase (5*k+5)) = _ at he
      rw [←show n+(m-n)=m by omega,run_add,h] at he; contradiction
    · rw [←show m+(n-m)=n by omega,run_add,show run m (phase (5*k+5))=_ from progress k,Option.bind_some] at h
      exact ih _ (by omega) (k+1) h

theorem never_blank (n : Nat) : run n blank ≠ none := by
  intro h
  by_cases hn : n≤30
  · have he := init; rw [←show n+(30-n)=30 by omega,run_add,h] at he; contradiction
  · rw [←show 30+(n-30)=n by omega,run_add,init,Option.bind_some] at h
    exact never_phase _ 0 h
#print axioms never_blank
end BB6.Agent13.Box33D14V18Growth
