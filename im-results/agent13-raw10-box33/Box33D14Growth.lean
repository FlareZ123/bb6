import C9PairConjugacy

namespace BB6.Agent13.Box33D14Growth
open C9Pair
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def z : Stream := fun _ => false
@[simp] theorem z_head : z 0 = false := rfl
@[simp] theorem z_pop : pop z = z := rfl
@[simp] theorem z_push : push false z = z := by funext n; cases n <;> rfl

def word : List Bool → Stream → Stream
  | [], s => s
  | a::as, s => push a (word as s)
@[simp] theorem word_nil (s : Stream) : word [] s = s := rfl
@[simp] theorem word_cons (b : Bool) (w : List Bool) (s : Stream) : word (b::w) s = push b (word w s) := rfl

def rep (w : List Bool) : Nat → Stream → Stream
  | 0,s => s
  | n+1,s => word w (rep w n s)
@[simp] theorem rep_zero (w : List Bool) (s : Stream) : rep w 0 s = s := rfl
@[simp] theorem rep_succ (w : List Bool) (n : Nat) (s : Stream) : rep w (n+1) s = word w (rep w n s) := rfl

theorem rep_add (w : List Bool) (m n : Nat) (s : Stream) : rep w (m+n) s = rep w m (rep w n s) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add,rep_succ,rep_succ,ih]

def cfg (q : Q) (l r : Stream) : Config := ⟨q,l,r 0,pop r⟩

def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .B false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (right .D false c)
  | .D,true => some (left .E false c)
  | .E,false => some (left .A true c)
  | .E,true => some (left .C true c)
  | .F,false => some (right .A true c)
  | .F,true => none

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step c <;> simp [ih]

abbrev ones := rep [true]
abbrev blocks := rep [false,false,true]
abbrev C (l r : Stream) := cfg .C l (word [true,true] r)
abbrev A (l r : Stream) := cfg .A l (word [false,true] r)

theorem begin (l : Stream) : run 2 (cfg .A l z) = some (C l z) := by
  simp [cfg,run,step,left,right]

theorem leftStep (l r : Stream) : run 3 (C (ones 3 l) r) = some (C l (blocks 1 r)) := by
  simp [cfg,run,step,left,right,ones,blocks,rep]

theorem leftSweep (n : Nat) (l r : Stream) : run (3*n) (C (ones (3*n) l) r) = some (C l (blocks n r)) := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega, show ones (3+3*n) l = ones 3 (ones (3*n) l) from rep_add _ _ _ _,run_add,leftStep,Option.bind_some,ih]
    rw [show blocks (n+1) r = blocks n (blocks 1 r) from rep_add _ _ _ _]

theorem turn (r : Stream) : run 3 (C (ones 1 z) r) = some (A z (blocks 1 r)) := by
  simp [cfg,run,step,left,right,ones,blocks,rep]

theorem rightStep (l r : Stream) : run 10 (A l (blocks 2 r)) = some (A (ones 6 l) r) := by
  simp [cfg,run,step,left,right,ones,blocks,rep]

theorem rightSweep (n : Nat) (l r : Stream) : run (10*n) (A l (blocks (2*n) r)) = some (A (ones (6*n) l) r) := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    rw [show 10*(n+1)=10+10*n by omega,show 2*(n+1)=2+2*n by omega,show blocks (2+2*n) r = blocks 2 (blocks (2*n) r) from rep_add _ _ _ _,run_add,rightStep,Option.bind_some,ih]
    rw [show 6*(n+1)=6*n+6 by omega,show ones (6*n+6) l = ones (6*n) (ones 6 l) from rep_add _ _ _ _]

theorem finish (l : Stream) : run 8 (A l z) = some (cfg .A (ones 4 l) z) := by
  simp [cfg,run,step,left,right,ones,blocks,rep]

def phase (k : Nat) : Config := cfg .A (ones (6*k+4) z) z

theorem growth (k : Nat) : run (16*k+26) (phase k) = some (phase (k+1)) := by
  unfold phase
  rw [show 16*k+26=2+3*(2*k+1)+3+10*(k+1)+8 by omega,run_add,run_add,run_add,run_add,begin,Option.bind_some]
  rw [show 6*k+4=3*(2*k+1)+1 by omega,show ones (3*(2*k+1)+1) z = ones (3*(2*k+1)) (ones 1 z) from rep_add _ _ _ _,leftSweep,Option.bind_some,turn,Option.bind_some]
  rw [show blocks 1 (blocks (2*k+1) z) = blocks (2*(k+1)) z by rw [show 2*(k+1)=1+(2*k+1) by omega]; exact (rep_add _ _ _ _).symm,rightSweep,Option.bind_some,finish]
  rw [show 6*(k+1)+4=4+6*(k+1) by omega,show ones (4+6*(k+1)) z = ones 4 (ones (6*(k+1)) z) from rep_add _ _ _ _]

def blank : Config := cfg .A z z

theorem init : run 15 blank = some (phase 0) := by
  simp [blank,phase,cfg,run,step,left,right,ones,rep]

theorem never_phase (n k : Nat) : run n (phase k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    by_cases hn : n ≤ 16*k+26
    · have h' := growth k
      rw [←show n+(16*k+26-n)=16*k+26 by omega,run_add,h] at h'
      contradiction
    · rw [←show (16*k+26)+(n-(16*k+26))=n by omega,run_add,growth,Option.bind_some] at h
      exact ih _ (by omega) (k+1) h

theorem never_blank (n : Nat) : run n blank ≠ none := by
  intro h
  by_cases hn : n ≤ 15
  · have h' := init
    rw [←show n+(15-n)=15 by omega,run_add,h] at h'
    contradiction
  · rw [←show 15+(n-15)=n by omega,run_add,init,Option.bind_some] at h
    exact never_phase (n-15) 0 h

#print axioms never_blank
end BB6.Agent13.Box33D14Growth
