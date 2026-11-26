import NatTape
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6WordNat
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6TwoSidedGuard BB6.Agent6NatTape

structure Word where
  len : Nat
  val : Nat
  deriving DecidableEq, BEq, Repr

def Word.empty : Word := ⟨0,0⟩
def Word.apply (w : Word) (tail : Nat) : Nat := w.val+2^w.len*tail
def Word.cat (a b : Word) : Word := ⟨a.len+b.len,a.apply b.val⟩
def Word.rep (w : Word) : Nat → Word
  | 0 => .empty
  | n+1 => w.cat (w.rep n)
def Word.valid (w : Word) : Prop := w.val < 2^w.len
instance (w : Word) : Decidable w.valid := inferInstanceAs (Decidable (w.val < 2^w.len))

theorem Word.empty_apply (t : Nat) : Word.empty.apply t = t := by simp [Word.empty,Word.apply]
theorem Word.cat_apply (a b : Word) (t : Nat) : (a.cat b).apply t = a.apply (b.apply t) := by
  simp only [Word.cat,Word.apply,Nat.pow_add,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]
theorem Word.cat_assoc (a b c : Word) : (a.cat b).cat c = a.cat (b.cat c) := by
  cases a; cases b; cases c
  simp [Word.cat,Word.apply,Nat.pow_add,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]
theorem Word.empty_cat (a : Word) : Word.empty.cat a = a := by cases a; simp [Word.cat,Word.empty,Word.apply]
theorem Word.cat_empty (a : Word) : a.cat .empty = a := by cases a; simp [Word.cat,Word.empty,Word.apply]
theorem Word.rep_add (a : Word) (n k : Nat) : a.rep (n+k) = (a.rep n).cat (a.rep k) := by
  induction n with
  | zero => simp [Word.rep,Word.empty_cat]
  | succ n ih => rw [Nat.succ_add,Word.rep,Word.rep,ih,Word.cat_assoc]
theorem Word.rep_succ_right (a : Word) (n : Nat) : a.rep (n+1) = (a.rep n).cat a := by
  rw [Word.rep_add]; simp [Word.rep,Word.cat_empty]
theorem Word.rep_rotate (a b : Word) (n : Nat) : ((a.cat b).rep n).cat a = a.cat ((b.cat a).rep n) := by
  induction n with
  | zero => simp [Word.rep,Word.empty_cat,Word.cat_empty]
  | succ n ih =>
    rw [Word.rep,Word.rep,Word.cat_assoc,ih,Word.cat_assoc]
    rw [←Word.cat_assoc b a]

/-- Numeric little-endian finite words, with exact length including zero padding. -/
def decodeBits : Nat → Nat → List Bool
  | 0,_ => []
  | n+1,v => head v :: decodeBits n (v/2)
def Word.decode (w : Word) : List Bool := decodeBits w.len w.val

theorem decodeBits_length (n v : Nat) : (decodeBits n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [decodeBits,ih]
theorem decodeBits_value (n v : Nat) (h : v < 2^n) : value (decodeBits n v) = v := by
  induction n generalizing v with
  | zero =>
    have hv : v=0 := by simpa using h
    subst v; rfl
  | succ n ih =>
    have hb : v/2 < 2^n := by rw [Nat.pow_succ] at h; omega
    simp only [decodeBits,value,ih _ hb,head]
    have hv : (v%2 == 1).toNat = v%2 := by
      have hh : v%2 = 0 ∨ v%2 = 1 := by omega
      rcases hh with h|h <;> simp [h]
    rw [hv]; omega

theorem Word.decode_length (w : Word) : w.decode.length = w.len := decodeBits_length _ _
theorem Word.decode_value (w : Word) (h : w.valid) : value w.decode = w.val := decodeBits_value _ _ h

theorem value_append (a b : List Bool) : value (a++b) = value a+2^a.length*value b := by
  induction a with
  | nil => simp [value]
  | cons a t ih =>
    simp only [List.cons_append,List.length_cons,value,ih,Nat.pow_succ,Nat.mul_add,Nat.add_assoc]
    rw [←Nat.mul_assoc, Nat.mul_comm 2 (2^t.length)]

theorem Word.value_apply (w : Word) (h : w.valid) (t : List Bool) : value (w.decode++t) = w.apply (value t) := by
  rw [value_append,Word.decode_length,Word.decode_value _ h]; rfl

theorem value_surj (n : Nat) : ∃ l : List Bool, value l = n := by
  have h : n < 2^(n+1) := by
    induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ]; omega
  exact ⟨decodeBits (n+1) n,decodeBits_value _ _ h⟩

structure Rule where
  leftIn : Word
  rightIn : Word
  leftOut : Word
  rightOut : Word
  cost : Nat
  deriving DecidableEq, Repr

def Rule.Valid (p : PartialMachine) (r : Rule) : Prop :=
  ∀ L R : Nat, runN p r.cost ⟨4,r.leftIn.apply L,r.rightIn.apply R⟩ =
    some ⟨4,r.leftOut.apply L,r.rightOut.apply R⟩

def Rule.check (p : PartialMachine) (r : Rule) : Bool :=
  decide (r.leftIn.valid ∧ r.rightIn.valid ∧ r.leftOut.valid ∧ r.rightOut.valid) &&
    decide (grun p r.cost ⟨4,r.leftIn.decode,r.rightIn.decode⟩ = some ⟨4,r.leftOut.decode,r.rightOut.decode⟩)

theorem Rule.sound (p : PartialMachine) (r : Rule) (h : r.check p = true) : r.Valid p := by
  simp only [Rule.check,Bool.and_eq_true,decide_eq_true_eq] at h
  intro L R
  obtain ⟨l,hl⟩ := value_surj L
  obtain ⟨r',hr⟩ := value_surj R
  have H := grun_append p r.cost l r' h.2
  have hE := run_encode p r.cost (appendBoth ⟨4,r.leftIn.decode,r.rightIn.decode⟩ l r')
  rw [H] at hE
  simp only [encode,appendBoth,Option.map_some,Word.value_apply _ h.1.1,Word.value_apply _ h.1.2.1,Word.value_apply _ h.1.2.2.1,Word.value_apply _ h.1.2.2.2,hl,hr] at hE
  exact hE

/-- The direction identifies which stack loses the repeated word. -/
structure Sweep where
  leftwards : Bool
  A : Word
  W : Word
  C : Word
  V : Word
  cost : Nat
  deriving DecidableEq, Repr

def Sweep.rule (s : Sweep) : Rule :=
  if s.leftwards then ⟨s.A.cat s.W,s.C,s.A,s.C.cat s.V,s.cost⟩
  else ⟨s.C,s.A.cat s.W,s.C.cat s.V,s.A,s.cost⟩
def Sweep.Valid (p : PartialMachine) (s : Sweep) := s.rule.Valid p

theorem Sweep.left (p : PartialMachine) (s : Sweep) (h : s.Valid p) (hd : s.leftwards = true)
    (n L R : Nat) : runN p (s.cost*n) ⟨4,s.A.apply ((s.W.rep n).apply L),s.C.apply R⟩ =
    some ⟨4,s.A.apply L,s.C.apply ((s.V.rep n).apply R)⟩ := by
  induction n generalizing R with
  | zero => simp only [Nat.mul_zero,Word.rep,Word.empty_apply]; rfl
  | succ n ih =>
    have h1 := h ((s.W.rep n).apply L) R
    simp only [Sweep.rule,hd,ite_true,Word.cat_apply] at h1
    have h2 := ih (s.V.apply R)
    have H := runN_join h1 h2
    rw [Nat.mul_succ,Nat.add_comm (s.cost*n)]
    rw [Word.rep,Word.cat_apply,Word.rep_succ_right s.V n,Word.cat_apply]
    exact H

theorem Sweep.right (p : PartialMachine) (s : Sweep) (h : s.Valid p) (hd : s.leftwards = false)
    (n L R : Nat) : runN p (s.cost*n) ⟨4,s.C.apply L,s.A.apply ((s.W.rep n).apply R)⟩ =
    some ⟨4,s.C.apply ((s.V.rep n).apply L),s.A.apply R⟩ := by
  induction n generalizing L with
  | zero => simp only [Nat.mul_zero,Word.rep,Word.empty_apply]; rfl
  | succ n ih =>
    have h1 := h L ((s.W.rep n).apply R)
    simp only [Sweep.rule,hd,Bool.false_eq_true,ite_false,Word.cat_apply] at h1
    have h2 := ih (s.V.apply L)
    have H := runN_join h1 h2
    rw [Nat.mul_succ,Nat.add_comm (s.cost*n)]
    rw [Word.rep,Word.cat_apply,Word.rep_succ_right s.V n,Word.cat_apply]
    exact H

#print axioms Rule.sound
#print axioms Sweep.left
#print axioms Sweep.right
end BB6.Agent6WordNat
