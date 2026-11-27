import Box33PrefixMacro
namespace BB6.Agent13.Box33ExactMacro
open C9Pair BB6.Agent13.Box33PrefixMacro
open BB6.Agent13.Box33D14Growth (z word)
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

structure ExactSpec (M L R : Type) where
  shape : M → Shape
  leftWord : L → List Bool
  rightWord : R → List Bool
  leftBase : Stream
  rightBase : Stream
  initial : M
  rule : M → Option L → Option R → Rule M L R

variable {M L R : Type}

def inStack {D : Type} (code : D → List Bool) (base : Stream) (d : Option D) (s : Stream) : Stream :=
  match d with
  | none => base
  | some d => word (code d) s

def outStack {D : Type} (code : D → List Bool) (base : Stream) (d : Option D) (ds : List D) (s : Stream) : Stream :=
  blocks code ds (if d.isSome then s else base)

def exactPhase (s : ExactSpec M L R) (m : M) (ls : List L) (rs : List R) : Config :=
  atShape (s.shape m) (blocks s.leftWord ls s.leftBase) (blocks s.rightWord rs s.rightBase)

def ExactSound (s : ExactSpec M L R) (step : Config → Option Config) : Prop :=
  ∀ m a d l r,
    run step (s.rule m a d).steps
      (atShape (s.shape m) (inStack s.leftWord s.leftBase a l)
        (inStack s.rightWord s.rightBase d r)) =
    some (atShape (s.shape (s.rule m a d).target)
      (outStack s.leftWord s.leftBase a (s.rule m a d).left l)
      (outStack s.rightWord s.rightBase d (s.rule m a d).right r))

def ExactPositive (s : ExactSpec M L R) : Prop := ∀ m a d, 0 < (s.rule m a d).steps

theorem exactProgress (s : ExactSpec M L R) (step : Config → Option Config)
    (hs : ExactSound s step) (ht : ExactPositive s) (m : M) (ls : List L) (rs : List R) :
    ∃ t : Nat, 0<t ∧ ∃ m' ls' rs', run step t (exactPhase s m ls rs) =
      some (exactPhase s m' ls' rs') := by
  cases ls with
  | nil =>
    cases rs with
    | nil =>
      let rr := s.rule m none none
      exact ⟨rr.steps,ht m none none,rr.target,rr.left,rr.right,
        by simpa [exactPhase,blocks,inStack,outStack,rr] using hs m none none s.leftBase s.rightBase⟩
    | cons d rs =>
      let rr := s.rule m none (some d)
      exact ⟨rr.steps,ht m none (some d),rr.target,rr.left,rr.right++rs,
        by simpa [exactPhase,blocks,inStack,outStack,blocks_append,rr] using
          hs m none (some d) s.leftBase (blocks s.rightWord rs s.rightBase)⟩
  | cons a ls =>
    cases rs with
    | nil =>
      let rr := s.rule m (some a) none
      exact ⟨rr.steps,ht m (some a) none,rr.target,rr.left++ls,rr.right,
        by simpa [exactPhase,blocks,inStack,outStack,blocks_append,rr] using
          hs m (some a) none (blocks s.leftWord ls s.leftBase) s.rightBase⟩
    | cons d rs =>
      let rr := s.rule m (some a) (some d)
      exact ⟨rr.steps,ht m (some a) (some d),rr.target,rr.left++ls,rr.right++rs,
        by simpa [exactPhase,blocks,inStack,outStack,blocks_append,rr] using
          hs m (some a) (some d) (blocks s.leftWord ls s.leftBase) (blocks s.rightWord rs s.rightBase)⟩

theorem exactNever (s : ExactSpec M L R) (step : Config → Option Config)
    (hs : ExactSound s step) (ht : ExactPositive s)
    (n : Nat) (m : M) (ls : List L) (rs : List R) :
    run step n (exactPhase s m ls rs) ≠ none := by
  induction n using Nat.strongRecOn generalizing m ls rs with
  | ind n ih =>
    intro h
    obtain ⟨t,ht',m',ls',rs',he⟩ := exactProgress s step hs ht m ls rs
    by_cases hn : n≤t
    · rw [←show n+(t-n)=t by omega,Box33PrefixMacro.run_add,h] at he
      contradiction
    · rw [←show t+(n-t)=n by omega,Box33PrefixMacro.run_add,he,Option.bind_some] at h
      exact ih _ (by omega) m' ls' rs' h

#print axioms exactNever
end BB6.Agent13.Box33ExactMacro
