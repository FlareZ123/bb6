import Lean

/-!
A local arithmetic proof of the token-cost and duration identities used in the
D Cryptid third-tail two-return case split. `wordCost` is reproduced verbatim
from `CryptidA.wordCost` in TokenCode.lean. This does not certify the machine
transition or padded-source bridges, which require original-source CI.
-/
namespace BB6.ThirdTailArithmetic

def inc : List Bool → Nat
  | [] => 0
  | false :: xs => 1 + inc xs
  | true :: xs => 4 + inc xs

def wc : Nat → List Bool → Nat
  | _, [] => 0
  | m, false :: xs => 2 + wc (m+1) xs
  | m, true :: xs => (6*m+41) + wc (m+4) xs

def tripleCost (m n : Nat) : Nat := n*(6*m+29)+12*n*n

def special (r : Nat) : List Bool :=
  List.replicate (2*r+1) true ++ false :: List.replicate 4 true

theorem inc_append (xs ys : List Bool) :
    inc (xs ++ ys) = inc xs + inc ys := by
  induction xs with
  | nil => simp [inc]
  | cons b xs ih =>
    cases b <;> simp [inc, ih, Nat.add_assoc]

theorem wc_append (m : Nat) (xs ys : List Bool) :
    wc m (xs ++ ys) = wc m xs + wc (m+inc xs) ys := by
  induction xs generalizing m with
  | nil => simp [inc, wc]
  | cons b xs ih =>
    cases b <;> simp [wc, inc, ih, Nat.add_assoc]

theorem inc_triples (n : Nat) :
    inc (List.replicate n true) = 4*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, inc, ih]
    omega

theorem wc_triples (m n : Nat) :
    wc m (List.replicate n true) = tripleCost m n := by
  induction n generalizing m with
  | zero => simp [wc, tripleCost]
  | succ n ih =>
    simp only [List.replicate_succ, wc]
    rw [ih]
    unfold tripleCost
    grind

theorem inc_special (r : Nat) : inc (special r) = 8*r+21 := by
  simp [special, inc_append, inc_triples, inc]
  grind

theorem wc_special (m r : Nat) :
    wc m (special r) =
      tripleCost m (2*r+1) + 2 +
        tripleCost (m+4*(2*r+1)+1) 4 := by
  unfold special
  rw [wc_append, wc_triples]
  rw [inc_triples]
  simp only [wc]
  rw [wc_triples]
  grind

/-- Case A: q = 3r+1, the 1100 padded terminal branch. -/
theorem a_first_mod_time (t r : Nat) :
    let K := 8*t+6
    let m := 4*K+3
    12*K*K+41*K+32 + wc m (special r) +
      (2*(m+inc (special r))+16) =
    48*r*r+384*r*t+638*r+768*t*t+2504*t+2103 := by
  dsimp
  rw [wc_special, inc_special]
  unfold tripleCost
  grind

/-- Case A: q = 3r+2, the zero-close branch. -/
theorem a_second_mod_time (t r : Nat) :
    let K := 8*t+6
    let m := 4*K+3
    let n := 2*r+2
    12*K*K+41*K+32 + wc m (List.replicate n true) +
      (2*(m+inc (List.replicate n true))+6) =
    48*r*r+384*r*t+494*r+768*t*t+1928*t+1216 := by
  dsimp
  rw [wc_triples, inc_triples]
  unfold tripleCost
  grind

/-- Case A: q = 3r+3, the 110111 terminal branch. -/
theorem a_third_mod_time (t r : Nat) :
    let K := 8*t+6
    let m := 4*K+3
    let n := 2*r+2
    12*K*K+41*K+32 + wc m (List.replicate n true) +
      (2*(m+inc (List.replicate n true))+24) =
    48*r*r+384*r*t+494*r+768*t*t+1928*t+1234 := by
  dsimp
  rw [wc_triples, inc_triples]
  unfold tripleCost
  grind

/-- The B second-return duration for initial k=3t. -/
theorem b_time (t : Nat) :
    12*(8*t+1)*(8*t+1)+49*(8*t+1)+40 =
    768*t*t+584*t+101 := by grind

/-- The E second-return duration for initial k=3t+1. -/
theorem e_time (t : Nat) :
    12*(8*t+3)*(8*t+3)+49*(8*t+3)+58 =
    768*t*t+968*t+313 := by grind

#print axioms inc_special
#print axioms wc_special
#print axioms a_first_mod_time
#print axioms a_second_mod_time
#print axioms a_third_mod_time
#print axioms b_time
#print axioms e_time
end BB6.ThirdTailArithmetic
