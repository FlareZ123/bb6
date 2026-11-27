import Box33SourceBridge
import Box17AuditCore
import Box33D14Growth

namespace BB6.Agent13.Box33D17V22M0
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .F false c)
  | .B,false => some (left .C true c)
  | .B,true => none
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .B false c)
  | .E,false => some (right .F false c)
  | .E,true => some (left .C false c)
  | .F,false => some (right .F true c)
  | .F,true => some (right .A false c)

def run : Nat → C9Pair.Config → Option C9Pair.Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : C9Pair.Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step c <;> simp [ih]


def five : List Bool := [true,true,true,true,true]
def block : List Bool := [true,false,false,false,true]
abbrev L (l r : Stream) := cfg .A (push false l) (word [false,false] r)
abbrev R (l r : Stream) := cfg .A (push false l) r

theorem leftStep (l r : Stream) :
    run 11 (L (word five l) r) = some (L l (word block r)) := by
  simp [L,R,five,block,cfg,run,step,left,right,word]
theorem turn0 (r : Stream) :
    run 8 (L z r) = some (R (word [true,true] z) r) := by
  simp [L,R,cfg,run,step,left,right,word]
theorem turn2 (r : Stream) :
    run 14 (L (word [true,true] z) r) = some (R (word five z) r) := by
  simp [L,R,five,cfg,run,step,left,right,word]
theorem rightStep (l r : Stream) :
    run 7 (R l (word block r)) = some (R (word five l) r) := by
  simp [L,R,five,block,cfg,run,step,left,right,word]

def leftTail (b : Bool) (k : Nat) : Stream :=
  rep five k (if b then word [true,true] z else z)
def rightTail (j : Nat) : Stream := rep block j z
def phase (s b : Bool) (k j : Nat) : C9Pair.Config :=
  if s then R (leftTail b k) (rightTail j) else L (leftTail b k) (rightTail j)

theorem progressL (b : Bool) (k j : Nat) :
    ∃ t : Nat, 0<t ∧ ∃ s' b' k' j', run t (phase false b k j) = some (phase s' b' k' j') := by
  cases k with
  | zero =>
    cases b
    · exact ⟨8,by decide,true,true,0,j,by simpa [phase,leftTail] using turn0 (rightTail j)⟩
    · exact ⟨14,by decide,true,false,1,j,by simpa [phase,leftTail] using turn2 (rightTail j)⟩
  | succ k =>
    exact ⟨11,by decide,false,b,k,j+1,
      by simpa [phase,leftTail,rightTail] using leftStep (leftTail b k) (rightTail j)⟩

theorem progress (s b : Bool) (k j : Nat) :
    ∃ t : Nat, 0<t ∧ ∃ s' b' k' j', run t (phase s b k j) = some (phase s' b' k' j') := by
  cases s
  · exact progressL b k j
  · cases j with
    | zero =>
      have he : phase true b k 0 = phase false b k 0 := by
        simp [phase,R,L,rightTail,word]
      rw [he]
      exact progressL b k 0
    | succ j =>
      exact ⟨7,by decide,true,b,k+1,j,
        by simpa [phase,leftTail,rightTail] using rightStep (leftTail b k) (rightTail j)⟩

theorem never_phase (n : Nat) (s b : Bool) (k j : Nat) :
    run n (phase s b k j) ≠ none := by
  induction n using Nat.strongRecOn generalizing s b k j with
  | ind n ih =>
    intro h
    obtain ⟨t,ht,s',b',k',j',he⟩ := progress s b k j
    by_cases hn : n≤t
    · rw [←show n+(t-n)=t by omega,run_add,h] at he
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) s' b' k' j' h

def blank : C9Pair.Config := cfg .A z z
theorem never_blank (n : Nat) : run n blank ≠ none := by
  simpa [blank,phase,leftTail,rightTail,L,word] using never_phase n false false 0 0

-- Source-faithful projection from the actual encoded residual.
open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,21,11,0,1,13,17,6,22,9,24,2]
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

#print axioms progress
#print axioms compatible_never
end BB6.Agent13.Box33D17V22M0
