import WordNat
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6SymWord
open BB6.Agent6WordNat

/-- Two independent repetition counters. The length of each block is fixed,
    but its contents may change under a certified sweep. -/
abbrev Var := Bool
abbrev Env := Var → Nat
structure Widths where
  x : Nat
  y : Nat
  deriving DecidableEq

def Widths.get (d : Widths) (v : Var) := if v then d.y else d.x
def env (x y : Nat) : Env := fun v => if v then y else x
def vary (v : Var) (n m : Nat) : Env := fun u => if u = v then n else m

inductive Atom where
  | lit (w : Word)
  | rep (w : Word) (v : Var)
  deriving DecidableEq, Repr
abbrev Sym := List Atom

def eval : Sym → Env → Nat
  | [],_ => 0
  | .lit w::t,e => w.apply (eval t e)
  | .rep w v::t,e => (w.rep (e v)).apply (eval t e)

def count (v : Var) : Sym → Nat
  | [] => 0
  | .lit _::t => count v t
  | .rep _ u::t => (if u = v then 1 else 0)+count v t

def lengths (d : Widths) : Sym → Bool
  | [] => true
  | .lit _::t => lengths d t
  | .rep w v::t => (w.len == d.get v) && lengths d t

def WF (d : Widths) (w : Sym) : Prop := count false w ≤ 1 ∧ count true w ≤ 1 ∧ lengths d w = true
instance (d : Widths) (w : Sym) : Decidable (WF d w) := inferInstanceAs (Decidable (count false w ≤ 1 ∧ count true w ≤ 1 ∧ lengths d w = true))

theorem eval_noVar (v : Var) (w : Sym) (h : count v w = 0) (n k m : Nat) :
    eval w (vary v n m) = eval w (vary v k m) := by
  induction w with
  | nil => rfl
  | cons a t ih =>
    cases a with
    | lit a => exact congrArg a.apply (ih h)
    | rep a u =>
      unfold count at h
      by_cases hu : u = v
      · simp [hu] at h
      · have ht : count v t = 0 := by simpa only [hu,ite_false,Nat.zero_add] using h
        simp only [eval,vary,hu,ite_false,ih ht]

/-- A scalar second-order linear recurrence, expressed without subtraction. -/
def Rec (A : Nat) (f : Nat → Nat) : Prop := ∀ n, f (n+2)+A*f n = (A+1)*f (n+1)

theorem Rec.constant (A c : Nat) : Rec A (fun _ => c) := by intro n; simp [Nat.add_mul,Nat.add_comm]

theorem Rec.affine {A : Nat} {f : Nat → Nat} (h : Rec A f) (b c : Nat) : Rec A (fun n => b+c*f n) := by
  intro n
  have hh := congrArg (fun t => c*t) (h n)
  simp only [Nat.mul_add,Nat.mul_assoc,Nat.add_mul,Nat.one_mul] at hh ⊢
  rw [←Nat.mul_assoc A c,Nat.mul_comm A c,Nat.mul_assoc c A]
  rw [←Nat.mul_assoc A c,Nat.mul_comm A c,Nat.mul_assoc c A]
  -- Rearrange the constant and recurrence terms.
  omega

theorem Rec.of_first {A b : Nat} {f : Nat → Nat} (h : ∀ n, f (n+1)=b+A*f n) : Rec A f := by
  intro n
  have h1 := h n
  have h2 := h (n+1)
  rw [h2,Nat.add_mul,Nat.one_mul]
  omega

theorem Rec.unique {A : Nat} {f g : Nat → Nat} (hf : Rec A f) (hg : Rec A g)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (n : Nat) : f n = g n := by
  have h (k : Nat) : f k = g k ∧ f (k+1) = g (k+1) := by
    induction k with
    | zero => exact ⟨h0,h1⟩
    | succ k ih =>
      refine ⟨ih.2,?_⟩
      have H := hf k
      have G := hg k
      rw [ih.1,ih.2] at H
      change f (k+2) = g (k+2)
      omega
  exact (h n).1

theorem eval_rec (d : Widths) (w : Sym) (v : Var) (hc : count v w ≤ 1) (hl : lengths d w = true) (m : Nat) :
    Rec (2^d.get v) (fun n => eval w (vary v n m)) := by
  induction w with
  | nil => exact Rec.constant _ _
  | cons a t ih =>
    cases a with
    | lit a =>
      have H := ih hc hl
      exact H.affine a.val (2^a.len)
    | rep a u =>
      simp only [lengths,Bool.and_eq_true,beq_iff_eq] at hl
      unfold count at hc
      by_cases hu : u = v
      · subst u
        have ht : count v t = 0 := by simp only [ite_true] at hc; omega
        apply Rec.of_first (b:=a.val)
        intro n
        change (a.rep (vary v (n+1) m v)).apply (eval t (vary v (n+1) m)) =
          a.val+2^d.get v*(a.rep (vary v n m v)).apply (eval t (vary v n m))
        simp only [vary,ite_true,Word.rep,Word.cat_apply]
        rw [eval_noVar v t ht (n+1) n m]
        rw [←hl.1]
        rfl
      · have ht : count v t ≤ 1 := by simpa only [hu,ite_false,Nat.zero_add] using hc
        have H := ih ht hl.2
        have H' := H.affine (a.rep m).val (2^(a.rep m).len)
        simpa only [eval,vary,hu,ite_false,Word.apply] using H'

theorem vary_false (n m : Nat) : vary false n m = env n m := by funext v; cases v <;> rfl
theorem vary_true (n m : Nat) : vary true n m = env m n := by funext v; cases v <;> rfl

/-- Four samples are a complete equality test for the two-counter symbolic
    words with at most one occurrence of each fixed-width repetition. -/
theorem sample_unique (d : Widths) (a b : Sym) (ha : WF d a) (hb : WF d b)
    (h00 : eval a (env 0 0) = eval b (env 0 0))
    (h10 : eval a (env 1 0) = eval b (env 1 0))
    (h01 : eval a (env 0 1) = eval b (env 0 1))
    (h11 : eval a (env 1 1) = eval b (env 1 1)) (x y : Nat) : eval a (env x y) = eval b (env x y) := by
  have hx0 := Rec.unique (eval_rec d a false ha.1 ha.2.2 0) (eval_rec d b false hb.1 hb.2.2 0)
    (by simpa only [vary_false] using h00) (by simpa only [vary_false] using h10) x
  have hx1 := Rec.unique (eval_rec d a false ha.1 ha.2.2 1) (eval_rec d b false hb.1 hb.2.2 1)
    (by simpa only [vary_false] using h01) (by simpa only [vary_false] using h11) x
  have hy := Rec.unique (eval_rec d a true ha.2.1 ha.2.2 x) (eval_rec d b true hb.2.1 hb.2.2 x)
    (by simpa only [vary_false,vary_true] using hx0) (by simpa only [vary_false,vary_true] using hx1) y
  simpa only [vary_true] using hy

def same (d : Widths) (a b : Sym) : Bool :=
  decide (WF d a ∧ WF d b ∧ eval a (env 0 0) = eval b (env 0 0) ∧
    eval a (env 1 0) = eval b (env 1 0) ∧ eval a (env 0 1) = eval b (env 0 1) ∧
    eval a (env 1 1) = eval b (env 1 1))

theorem same_sound (d : Widths) (a b : Sym) (h : same d a b = true) (x y : Nat) : eval a (env x y) = eval b (env x y) := by
  simp only [same,decide_eq_true_eq] at h
  exact sample_unique d a b h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 x y

#print axioms sample_unique
#print axioms same_sound
end BB6.Agent6SymWord
