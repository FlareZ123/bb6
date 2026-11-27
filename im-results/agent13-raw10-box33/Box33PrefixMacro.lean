import Box33SourceBridge
import Box17AuditCore
import Box33D14Growth

namespace BB6.Agent13.Box33PrefixMacro
open C9Pair
open BB6.Agent13.Box33D14Growth (z word)
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def run (step : Config → Option Config) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run step n)

theorem run_add (step : Config → Option Config) (m n : Nat) (c : Config) :
    run step (m+n) c = (run step m c).bind (run step n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step c <;> simp [ih]

structure Shape where
  q : Q
  a : Bool
  lpre : List Bool
  rpre : List Bool

def atShape (p : Shape) (l r : Stream) : Config :=
  ⟨p.q,word p.lpre l,p.a,word p.rpre r⟩

def blocks {D : Type} (code : D → List Bool) : List D → Stream → Stream
  | [],r => r
  | d::ds,r => word (code d) (blocks code ds r)

theorem blocks_append {D : Type} (code : D → List Bool) (xs ys : List D) (r : Stream) :
    blocks code (xs++ys) r = blocks code xs (blocks code ys r) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [blocks,ih]

structure Rule (M L R : Type) where
  steps : Nat
  target : M
  left : List L
  right : List R

structure Spec (M L R : Type) where
  shape : M → Shape
  leftWord : L → List Bool
  rightWord : R → List Bool
  initial : M
  zeroDigit : R
  rule : M → Option L → R → Rule M L R

variable {M L R : Type}

def phase (s : Spec M L R) (m : M) (ls : List L) (rs : List R) : Config :=
  atShape (s.shape m) (blocks s.leftWord ls z) (blocks s.rightWord rs z)

def inLeft (s : Spec M L R) (a : Option L) (l : Stream) : Stream :=
  match a with
  | none => z
  | some a => word (s.leftWord a) l

def outLeft (s : Spec M L R) (a : Option L) (rr : Rule M L R) (l : Stream) : Stream :=
  blocks s.leftWord rr.left (if a.isSome then l else z)

def Sound (s : Spec M L R) (step : Config → Option Config) : Prop :=
  ∀ m a d l r,
    run step (s.rule m a d).steps
      (atShape (s.shape m) (inLeft s a l) (word (s.rightWord d) r)) =
    some (atShape (s.shape (s.rule m a d).target)
      (outLeft s a (s.rule m a d) l) (blocks s.rightWord (s.rule m a d).right r))

def Positive (s : Spec M L R) : Prop := ∀ m a d, 0 < (s.rule m a d).steps

theorem progressCons (s : Spec M L R) (step : Config → Option Config)
    (hs : Sound s step) (ht : Positive s) (m : M) (ls : List L) (d : R) (rs : List R) :
    ∃ t : Nat, 0<t ∧ ∃ m' ls' rs', run step t (phase s m ls (d::rs)) =
      some (phase s m' ls' rs') := by
  cases ls with
  | nil =>
    let rr := s.rule m none d
    exact ⟨rr.steps,ht m none d,rr.target,rr.left,rr.right++rs,
      by simpa [phase,blocks,inLeft,outLeft,blocks_append,rr] using
        hs m none d z (blocks s.rightWord rs z)⟩
  | cons a ls =>
    let rr := s.rule m (some a) d
    exact ⟨rr.steps,ht m (some a) d,rr.target,rr.left++ls,rr.right++rs,
      by simpa [phase,blocks,inLeft,outLeft,blocks_append,rr] using
        hs m (some a) d (blocks s.leftWord ls z) (blocks s.rightWord rs z)⟩

theorem progress (s : Spec M L R) (step : Config → Option Config)
    (hs : Sound s step) (ht : Positive s) (hz : word (s.rightWord s.zeroDigit) z = z)
    (m : M) (ls : List L) (rs : List R) :
    ∃ t : Nat, 0<t ∧ ∃ m' ls' rs', run step t (phase s m ls rs) =
      some (phase s m' ls' rs') := by
  cases rs with
  | nil =>
    have he : phase s m ls [] = phase s m ls [s.zeroDigit] := by simp [phase,blocks,hz]
    rw [he]
    exact progressCons s step hs ht m ls s.zeroDigit []
  | cons d rs => exact progressCons s step hs ht m ls d rs

theorem neverPhase (s : Spec M L R) (step : Config → Option Config)
    (hs : Sound s step) (ht : Positive s) (hz : word (s.rightWord s.zeroDigit) z = z)
    (n : Nat) (m : M) (ls : List L) (rs : List R) :
    run step n (phase s m ls rs) ≠ none := by
  induction n using Nat.strongRecOn generalizing m ls rs with
  | ind n ih =>
    intro h
    obtain ⟨t,ht',m',ls',rs',he⟩ := progress s step hs ht hz m ls rs
    by_cases hn : n≤t
    · rw [←show n+(t-n)=t by omega,run_add,h] at he
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) m' ls' rs' h

open BB6Coverage
abbrev project := Box33Source.project false

theorem map_step (m : Machine) (c : BB6Coverage.Config) :
    (rawStep m c).map project =
      match m (readSlot c) with
      | none => none
      | some mv => some (if mv.right then C9Pair.right (Box33Source.q false mv.next) mv.write (project c)
                         else C9Pair.left (Box33Source.q false mv.next) mv.write (project c)) := by
  unfold rawStep
  cases ht : m (readSlot c) with
  | none => rfl
  | some mv => simp only [Option.map_some,Box33Source.project_applyMove]

theorem project_run (m : Machine) (step : C9Pair.Config → Option C9Pair.Config)
    (hstep : ∀ c, (rawStep m c).map project = step (project c))
    (n : Nat) (c : BB6Coverage.Config) :
    (BB6Coverage.run m n c).map project = run step n (project c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_add _ n 1,←ih]
    simp only [BB6Coverage.run]
    cases ht : BB6Coverage.run m n c with
    | none => rfl
    | some c' =>
      simp only [Option.bind_some,Option.map_some]
      simpa [run] using hstep c'

theorem sourceNever (m : Machine) (step : C9Pair.Config → Option C9Pair.Config)
    (hstep : ∀ c, (rawStep m c).map project = step (project c))
    (hn : ∀ n, run step n (project BB6Coverage.blank) ≠ none) : NeverHalts m := by
  intro n
  have he := project_run m step hstep n BB6Coverage.blank
  cases hr : BB6Coverage.run m n BB6Coverage.blank with
  | none =>
    rw [hr] at he
    exact False.elim (hn n he.symm)
  | some c => rfl

#print axioms neverPhase
#print axioms sourceNever
end BB6.Agent13.Box33PrefixMacro
