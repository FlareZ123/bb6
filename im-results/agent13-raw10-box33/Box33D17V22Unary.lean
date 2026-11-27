import Box33SourceBridge
import Box17AuditCore
import Box33D14Growth

namespace BB6.Agent13.Box33D17V22Unary
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .A true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .C false c)
  | .E,false => some (right .F false c)
  | .E,true => none
  | .F,false => some (left .A true c)
  | .F,true => some (right .D false c)

def run : Nat → C9Pair.Config → Option C9Pair.Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : C9Pair.Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step c <;> simp [ih]

abbrev L (l r : Stream) := cfg .A l (word [false,false] r)
abbrev R (l r : Stream) := cfg .A l (push false r)

theorem leftStep (l r : Stream) :
    run 5 (L (ones 1 l) r) = some (L l (ones 1 r)) := by
  simp [L,cfg,run,step,left,right,ones,rep,word]

theorem leftSweep (n : Nat) (l r : Stream) :
    run (5*n) (L (ones n l) r) = some (L l (ones n r)) := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,
        show ones (n+1) l = ones 1 (ones n l) by
          rw [show n+1=1+n by omega]; exact rep_add _ _ _ _,
        run_add,leftStep,Option.bind_some,ih]
    rw [show ones (n+1) r = ones n (ones 1 r) from rep_add _ _ _ _]

theorem turn (r : Stream) :
    run 8 (L z r) = some (R (ones 2 z) (ones 1 r)) := by
  simp [L,R,cfg,run,step,left,right,ones,rep,word]

theorem rightStep (l r : Stream) :
    run 11 (R l (ones 5 r)) = some (R (ones 5 l) r) := by
  simp [R,cfg,run,step,left,right,ones,rep,word]

theorem rightSweep (n : Nat) (l r : Stream) :
    run (11*n) (R l (ones (5*n) r)) = some (R (ones (5*n) l) r) := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    rw [show 11*(n+1)=11+11*n by omega,
        show 5*(n+1)=5+5*n by omega,
        show ones (5+5*n) r = ones 5 (ones (5*n) r) from rep_add _ _ _ _,
        run_add,rightStep,Option.bind_some,ih]
    rw [show ones (5+5*n) l = ones (5*n) (ones 5 l) by
      rw [show 5+5*n=5*n+5 by omega]; exact rep_add _ _ _ _]

theorem finish (l : Stream) :
    run 9 (R l (ones 3 z)) = some (L (ones 5 l) z) := by
  simp [L,R,cfg,run,step,left,right,ones,rep,word]

def phase (k : Nat) : C9Pair.Config := L (ones (5*k+7) z) z
def blank : C9Pair.Config := cfg .A z z

theorem init : run 49 blank = some (phase 0) := by
  have h0 : run 10 blank = some (L (ones 4 z) z) := by
    simp [blank,L,cfg,run,step,left,right,ones,rep,word]
  have h1 : run 20 (L (ones 4 z) z) = some (L z (ones 4 z)) := leftSweep 4 z z
  have h2 : run 11 (R (ones 2 z) (ones 1 (ones 4 z))) = some (R (ones 7 z) z) := by
    simpa [ones,rep,word] using rightStep (ones 2 z) z
  rw [show 49=10+20+8+11 by decide,run_add,run_add,run_add,h0,Option.bind_some,h1,Option.bind_some,turn,Option.bind_some,h2]
  simp [phase,L,R,word]

theorem growth (k : Nat) : run (36*k+63) (phase k) = some (phase (k+1)) := by
  unfold phase
  rw [show 36*k+63=5*(5*k+7)+8+11*(k+1)+9 by omega,
      run_add,run_add,run_add,leftSweep,Option.bind_some,turn,Option.bind_some]
  rw [show ones 1 (ones (5*k+7) z) = ones (5*(k+1)+3) z by
      calc
        _ = ones (1+(5*k+7)) z := (rep_add [true] 1 (5*k+7) z).symm
        _ = _ := by rw [show 1+(5*k+7)=5*(k+1)+3 by omega],
      show ones (5*(k+1)+3) z = ones (5*(k+1)) (ones 3 z) from rep_add _ _ _ _,
      rightSweep,Option.bind_some,finish]
  have he : ones 5 (ones (5*(k+1)) (ones 2 z)) = ones (5*(k+1)+7) z := by
    calc
      _ = ones 5 (ones (5*(k+1)+2) z) := congrArg (ones 5) (rep_add [true] (5*(k+1)) 2 z).symm
      _ = ones (5+(5*(k+1)+2)) z := (rep_add [true] 5 (5*(k+1)+2) z).symm
      _ = _ := by rw [show 5+(5*(k+1)+2)=5*(k+1)+7 by omega]
  rw [he]

theorem never_phase (n k : Nat) : run n (phase k) ≠ none := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    intro h
    by_cases hn : n ≤ 36*k+63
    · have he := growth k
      rw [←show n+(36*k+63-n)=36*k+63 by omega,run_add,h] at he
      contradiction
    · rw [←show (36*k+63)+(n-(36*k+63))=n by omega,run_add,growth,Option.bind_some] at h
      exact ih _ (by omega) (k+1) h

theorem never_blank (n : Nat) : run n blank ≠ none := by
  intro h
  by_cases hn : n≤49
  · have he := init
    rw [←show n+(49-n)=49 by omega,run_add,h] at he
    contradiction
  · rw [←show 49+(n-49)=n by omega,run_add,init,Option.bind_some] at h
    exact never_phase _ 0 h

-- Source-faithful projection from the actual encoded residual.
open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,24,11,4,1,13,17,10,22,0,3,14]
def table : Machine := fun s => decode (codes.getD (index s).val 0)
abbrev project := Box33Source.project false

theorem map_step (c : BB6Coverage.Config) :
    (rawStep table c).map project =
      match table (readSlot c) with
      | none => none
      | some mv => some (if mv.right then C9Pair.right (Box33Source.q false mv.next) mv.write (project c)
                         else C9Pair.left (Box33Source.q false mv.next) mv.write (project c)) := by
  unfold rawStep
  cases ht : table (readSlot c) with
  | none => rfl
  | some mv => simp only [Option.map_some,Box33Source.project_applyMove]

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem project_run (n : Nat) (c : BB6Coverage.Config) :
    (BB6Coverage.run table n c).map project = run n (project c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_add n 1,←ih]
    simp only [BB6Coverage.run]
    cases ht : BB6Coverage.run table n c with
    | none => rfl
    | some c' =>
      simp only [Option.bind_some,Option.map_some]
      simpa [run] using project_step c'

theorem never : NeverHalts table := by
  intro n
  have he := project_run n BB6Coverage.blank
  have hn : run n (project BB6Coverage.blank) ≠ none := never_blank n
  cases hr : BB6Coverage.run table n BB6Coverage.blank with
  | none =>
    rw [hr] at he
    exact False.elim (hn he.symm)
  | some c => rfl

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms growth
#print axioms compatible_never
end BB6.Agent13.Box33D17V22Unary
