-- Exact 2^k-bit sweep algebra underlying the published accelerated row109 simulator.
namespace BB6Row109GF2

inductive Bits : Nat → Type
  | leaf : Bool → Bits 0
  | join {k : Nat} : Bits k → Bits k → Bits (k+1)
  deriving Repr, DecidableEq

namespace Bits

def xor : {k : Nat} → Bits k → Bits k → Bits k
  | 0, .leaf a, .leaf b => .leaf (a ^^ b)
  | _ + 1, .join a b, .join c d => .join (xor a c) (xor b d)

-- S maps incoming head bits into the outgoing data-symbol correction.
def s : {k : Nat} → Bits k → Bits k
  | 0, .leaf a => .leaf a
  | _ + 1, .join a b => .join (s (xor a b)) (s a)

-- T maps input data-symbol bits into the outgoing head correction.
def t : {k : Nat} → Bits k → Bits k
  | 0, .leaf a => .leaf a
  | _ + 1, .join a b => .join (t b) (t (xor a b))

def zero : {k : Nat} → Bits k
  | 0 => .leaf false
  | _ + 1 => .join zero zero

-- A single head-bit sweep crossing a single digit has the exact local rule:
-- input head h, digit b -> output data b xor h; output head b xor h xor 1.
-- The 'first' bit constant is in the first position of the *head* vector.
def e : {k : Nat} → Bits k
  | 0 => .leaf true
  | _ + 1 => .join e zero

-- 2^k-ary vectorized longitudinal sweep.
def sweep {k : Nat} (heads digits : Bits k) : Bits k × Bits k :=
  (xor digits (s heads), xor (xor heads (t digits)) e)

-- XOR structural algebra on perfect balanced bit trees.
theorem xor_assoc : ∀ {k : Nat} (a b c : Bits k), xor (xor a b) c = xor a (xor b c)
  | 0, .leaf a, .leaf b, .leaf c => by simp [xor]
  | _ + 1, .join a b, .join c d, .join e f => by simp [xor, xor_assoc]

theorem xor_comm {k : Nat} (a b : Bits k) : xor a b = xor b a := by
  induction a with
  | leaf a => cases b with | leaf b => simp [xor, Bool.xor_comm]
  | join a b ha hb => cases b with | join c d => simp [xor, ha, hb]

theorem xor_self {k : Nat} (a : Bits k) : xor a a = zero := by
  induction a with
  | leaf a => simp [xor, zero]
  | join a b ha hb => simp [xor, zero, ha, hb]

theorem xor_zero {k : Nat} (a : Bits k) : xor a zero = a := by
  induction a with
  | leaf a => simp [xor, zero]
  | join a b ha hb => simp [xor, zero, ha, hb]

theorem xor_zero_left {k : Nat} (a : Bits k) : xor zero a = a := by
  rw [xor_comm, xor_zero]

theorem xor_swap {k : Nat} (a b c : Bits k) :
    xor (xor a b) (xor b c) = xor a c := by
  rw [xor_assoc, ← xor_assoc b b c, xor_self, xor_zero_left]

theorem xor_exchange {k : Nat} (a b c d : Bits k) :
    xor (xor a c) (xor b d) = xor (xor a b) (xor c d) := by
  calc
    xor (xor a c) (xor b d) = xor a (xor c (xor b d)) := by rw [xor_assoc]
    _ = xor a (xor b (xor c d)) := by
      rw [← xor_assoc c b d, xor_comm c b, xor_assoc b c d]
    _ = xor (xor a b) (xor c d) := by rw [xor_assoc]

theorem xor_cancel_left {k : Nat} (a b : Bits k) : xor a (xor a b) = b := by
  rw [← xor_assoc, xor_self, xor_zero_left]

theorem xor_cancel_right {k : Nat} (a b : Bits k) : xor b (xor a b) = a := by
  rw [xor_comm a b, xor_cancel_left]

theorem s_linear : ∀ {k : Nat} (a b : Bits k), s (xor a b) = xor (s a) (s b) := by
  intro k
  induction k with
  | zero =>
      intro a b
      cases a with
      | leaf a => cases b with | leaf b => simp [s, xor]
  | succ k ih =>
      intro a b
      cases a with
      | join a1 a2 =>
          cases b with
          | join b1 b2 =>
              simp only [xor, s]
              rw [xor_exchange a1 a2 b1 b2]
              simp [ih]

theorem t_linear : ∀ {k : Nat} (a b : Bits k), t (xor a b) = xor (t a) (t b) := by
  intro k
  induction k with
  | zero =>
      intro a b
      cases a with
      | leaf a => cases b with | leaf b => simp [t, xor]
  | succ k ih =>
      intro a b
      cases a with
      | join a1 a2 =>
          cases b with
          | join b1 b2 =>
              simp only [xor, t]
              rw [xor_exchange a1 a2 b1 b2]
              simp [ih]

-- T is an exact two-sided inverse of S, at EVERY power-of-two block length.
theorem ts_id : ∀ {k : Nat} (a : Bits k), t (s a) = a := by
  intro k
  induction k with
  | zero =>
      intro a
      cases a <;> rfl
  | succ k ih =>
      intro a
      cases a with
      | join a b =>
          simp only [s, t]
          rw [t_linear, ih a, ih (xor a b)]
          rw [xor_comm (xor a b) a, xor_cancel_left a b]

theorem st_id : ∀ {k : Nat} (a : Bits k), s (t a) = a := by
  intro k
  induction k with
  | zero =>
      intro a
      cases a <;> rfl
  | succ k ih =>
      intro a
      cases a with
      | join a b =>
          simp only [t, s]
          rw [s_linear, ih b, ih (xor a b)]
          rw [xor_cancel_right a b]

-- Both output streams obey an algebraically necessary compatibility law.
theorem sweep_output_relation {k : Nat} (heads digits : Bits k) :
    (sweep heads digits).2 = xor (t (sweep heads digits).1) e := by
  dsimp [sweep]
  rw [t_linear, ts_id]
  rw [xor_comm heads (t digits)]

#print axioms BB6Row109GF2.Bits.ts_id
#print axioms BB6Row109GF2.Bits.st_id
#print axioms BB6Row109GF2.Bits.sweep_output_relation
end Bits
end BB6Row109GF2
