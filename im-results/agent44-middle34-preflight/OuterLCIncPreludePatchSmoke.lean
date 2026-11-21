import Lean.Elab.Tactic.Omega

def d0 : List Bool := [false,false,true]
def d1 : List Bool := [true,true,true]
def d1pow : Nat → List Bool
  | 0 => []
  | n+1 => d1 ++ d1pow n

def sideBit : List Bool → Nat → Bool
  | [], _ => false
  | h::_, 0 => h
  | _::t, n+1 => sideBit t n

theorem d1pow_length (n : Nat) : (d1pow n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [d1pow,d1,ih,Nat.mul_succ]

theorem outer_sideBit_append_shift (xs ys : List Bool) (i : Nat) :
    sideBit (xs ++ ys) (xs.length+i) = sideBit ys i := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, Nat.succ_add, List.cons_append]
      exact ih i

/-- The exact zero-boundary proof shape used in OuterLCIncPrelude: the
index is the prefix length, so instantiate append-shift at offset zero. -/
theorem zero_at_d1pow_boundary (r : Nat) (ys : List Bool) :
    sideBit (d1pow r ++ d0 ++ ys) (3*r) = false := by
  have hrest : d1pow r ++ d0 ++ ys = d1pow r ++ (d0 ++ ys) := by
    simp [List.append_assoc]
  rw [hrest, ← d1pow_length r]
  simpa [d0, sideBit] using
    (outer_sideBit_append_shift (d1pow r) (d0 ++ ys) 0)

/-- The exact Int-coordinate normalization used to align the H-run endpoint. -/
theorem head_normalization (a m : Nat) (h : Int) :
    h - (3*a : Int) - (m+5 : Int) + 2 =
      h - (3*a+m+5 : Int) + 2 := by
  omega

#print axioms zero_at_d1pow_boundary
#print axioms head_normalization
