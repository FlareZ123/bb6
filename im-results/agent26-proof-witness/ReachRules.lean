module
public import Init
@[expose] public section
namespace ReachRules

variable {C : Type}

def run (step : C → C) (n : Nat) (c : C) : C := match n with
  | 0 => c
  | k+1 => run step k (step c)

def ReachesIn (step : C → C) (n : Nat) (a b : C) : Prop := run step n a = b

def ReachesStar (step : C → C) (a b : C) : Prop := ∃ n, ReachesIn step n a b

def ReachesPlus (step : C → C) (a b : C) : Prop := ∃ n, n > 0 ∧ ReachesIn step n a b

theorem run_add (f : C → C) (m n : Nat) (c : C) :
    run f (m+n) c = run f n (run f m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [show m+1+n=m+n+1 by omega]
    exact ih (f c)

theorem ReachesStar.trans {f : C → C} {a b c : C}
    (h₁ : ReachesStar f a b) (h₂ : ReachesStar f b c) : ReachesStar f a c := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  refine ⟨m+n, ?_⟩
  unfold ReachesIn at *
  rw [run_add, hm, hn]

theorem ReachesPlus.toStar {f : C → C} {a b : C} (h : ReachesPlus f a b) : ReachesStar f a b := by
  obtain ⟨n, _, h⟩ := h
  exact ⟨n,h⟩

theorem ReachesPlus.head {f : C → C} {a b c : C}
    (h₁ : f a = b) (h₂ : ReachesStar f b c) : ReachesPlus f a c := by
  obtain ⟨n, hn⟩ := h₂
  exact ⟨n+1, by omega, by simpa [ReachesIn,run,h₁] using hn⟩

/-- A concrete stack transfer model. It reads the next right cell (implicit zero)
    and writes one on the left before moving right. -/
structure Cfg where
  left : List Bool
  right : List Bool
  deriving DecidableEq

def move (c : Cfg) : Cfg := ⟨true :: c.left, c.right.tail⟩

def config (l r : List Bool) : Cfg := ⟨l,r⟩

theorem single (l r : List Bool) (b : Bool) : ReachesStar move (config l (b::r)) (config (true::l) r) := ⟨1,rfl⟩

/-- This proof deliberately erases the primitive count. -/
theorem triple (l r : List Bool) : ReachesPlus move
    (config l (false::true::false::r)) (config (true::true::true::l) r) := by
  apply ReachesPlus.head (b := config (true::l) (true::false::r)) rfl
  exact ReachesStar.trans (single (true::l) (false::r) true) (single (true::true::l) r false)

theorem triple_rewrite (l r : List Bool) : ReachesPlus move
    (config l (false::true::false::r)) (config (List.replicate 3 true ++ l) r) := by
  simpa only [List.replicate_succ, List.replicate_zero, List.nil_append, List.cons_append] using triple l r

theorem sweep (n : Nat) (l r : List Bool) : ReachesStar move
    (config l (List.replicate n false ++ r)) (config (List.replicate n true ++ l) r) := by
  induction n generalizing l with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    rw [List.replicate_succ', List.append_assoc]
    exact ReachesStar.trans (single l (List.replicate n false ++ r) false) (ih (true::l))

end ReachRules
