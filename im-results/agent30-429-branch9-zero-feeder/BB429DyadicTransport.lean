import Lean.Elab.Tactic.Omega

namespace BB429DyadicTransport

/-- Weighted precision: first coordinate modulo m, second modulo 2m.
    Signed representatives permit exact inverse equations without truncation. -/
def Near (m a b x y : Int) : Prop :=
  ∃ i j : Int, x - a = m*i ∧ y-b = (2*m)*j

/-- First inverse: doubling/subtraction branch. -/
theorem first (m a b x y a' b' x' y' : Int)
    (h : Near (2*m) a b x y)
    (ha : a = 2*a'+3) (hx : x = 2*x'+3)
    (hb : b' = b+a) (hy : y' = y+x) :
    Near m a' b' x' y' := by
  obtain ⟨i,j,hi,hj⟩ := h
  refine ⟨i,i+2*j,?_,?_⟩
  · rw [Int.mul_assoc] at hi
    omega
  · rw [Int.mul_add, Int.mul_left_comm (2*m) 2 j, Int.mul_assoc 2 m i]
    rw [Int.mul_assoc] at hi
    have hh : (2 * (2*m))*j = 2*((2*m)*j) := by rw [Int.mul_assoc]
    rw [hh] at hj
    omega

/-- Exceptional inverse: applies to S and E, differing only by constants. -/
theorem exceptional (m a b x y a' b' x' y' c e : Int)
    (h : Near (2*m) a b x y)
    (ha : 4*a'+c = 4*a+b) (hx : 4*x'+c = 4*x+y)
    (hb : 2*b' = b+e) (hy : 2*y' = y+e) :
    Near m a' b' x' y' := by
  obtain ⟨i,j,hi,hj⟩ := h
  refine ⟨2*i+j,j,?_,?_⟩
  · rw [Int.mul_add, Int.mul_left_comm m 2 i]
    rw [Int.mul_assoc] at hi
    have hh : (2 * (2*m))*j = 4*(m*j) := by
      rw [← Int.mul_assoc 2 2 m, Int.mul_assoc]
      rfl
    rw [hh] at hj
    omega
  · have hh : (2 * (2*m))*j = 2*((2*m)*j) := by rw [Int.mul_assoc]
    rw [hh] at hj
    omega

/-- Reduce weighted precision without changing representatives. -/
theorem half (m a b x y : Int) (h : Near (2*m) a b x y) :
    Near m a b x y := by
  obtain ⟨i,j,hi,hj⟩ := h
  refine ⟨2*i,2*j,?_,?_⟩
  · rw [Int.mul_left_comm m 2 i, ← Int.mul_assoc]
    exact hi
  · rw [Int.mul_left_comm (2*m) 2 j, ← Int.mul_assoc]
    exact hj

/-- The exact scale used by the existing ghost sieve, at remaining depth d. -/
def scale : Nat → Int
  | 0 => 64
  | d+1 => 2*scale d

theorem nearBase (d : Nat) (a b x y : Int)
    (h : Near (scale d) a b x y) : Near 64 a b x y := by
  induction d with
  | zero => exact h
  | succ d ih => exact ih (half _ _ _ _ _ h)

/-- Signed inverse tree: all branches retained by the parity grammar. The
    caller supplies a root-necessary filter on the 64/128 base precision.
    The search is deliberately an overapproximation of natural predecessors. -/
def search (test : Int → Int → Bool) : Nat → Int → Int → Bool
  | 0, a, b => test a b
  | d+1, a, b => test a b &&
      ((if a%2=1 then search test d ((a-3)/2) (a+b) else false) ||
       (if b%4=2 then
          if a%2=1 then search test d ((4*a+b-26)/4) ((b+4)/2)
          else search test d ((4*a+b-14)/4) (b/2)
        else false))

/-- Genuine rooted high-output predecessors, stated abstractly so the
    finite checker has no dependency on any particular root predicate. -/
def InverseGrammar (R : Nat → Nat → Prop) : Prop :=
  (∀ a b, 13 ≤ a → a%2=1 → R a b →
    (∃ x y, R x y ∧ a=2*x+3 ∧ y=a+b) ∨
    (∃ x y, R x y ∧ 4*x+26=4*a+b ∧ 2*y=b+4 ∧ b%4=2)) ∧
  (∀ a b, 13 ≤ a → a%2=0 → R a b →
    ∃ x y, R x y ∧ 4*x+14=4*a+b ∧ 2*y=b ∧ b%4=2)

/-- A failed signed search excludes every genuine sufficiently high state
    in the entire weighted congruence cylinder. No assumption of actual
    reachability of a successful search path is made. -/
theorem search_sound (R : Nat → Nat → Prop) (grammar : InverseGrammar R)
    (test : Int → Int → Bool)
    (test_sound : ∀ a b x y, 33 ≤ x → R x y → Near 64 a b x y → test a b = true)
    (d : Nat) (a b : Int) (x y : Nat)
    (high : 36*2^d ≤ x+3) (root : R x y)
    (near : Near (scale d) a b x y) : search test d a b = true := by
  induction d generalizing a b x y with
  | zero => exact test_sound a b x y (by simp at high; omega) root near
  | succ d ih =>
    have hx : 33 ≤ x := by
      have h : 0 < (2:Nat)^(d+1) := Nat.two_pow_pos (d+1)
      omega
    have base := nearBase (d+1) a b x y near
    have ht := test_sound a b x y hx root base
    have hxhigh : 36*2^d*2 ≤ x+3 := by simpa [Nat.pow_succ, Nat.mul_assoc] using high
    obtain ⟨i,j,hi,hj⟩ := base
    have ha : a%2 = (x:Int)%2 := by omega
    have hb : b%4 = (y:Int)%4 := by omega
    have near' : Near (2*scale d) a b x y := near
    rw [search, ht]
    simp only [Bool.true_and, Bool.or_eq_true]
    by_cases hodd : x%2=1
    · have haodd : a%2=1 := by omega
      rcases grammar.1 x y (by omega) hodd root with hF | hS
      · obtain ⟨u,v,hr,hu,hv⟩ := hF
        have hhigh : 36*2^d ≤ u+3 := by omega
        have hnear := first (scale d) a b x y ((a-3)/2) (a+b) u v near'
          (by omega) (by omega) (by omega) (by omega)
        left
        rw [ite_eq_left haodd]
        exact ih _ _ _ _ hhigh hr hnear
      · obtain ⟨u,v,hr,hu,hv,hmod⟩ := hS
        have hb2 : b%4=2 := by omega
        have hhigh : 36*2^d ≤ u+3 := by omega
        have hnear := exceptional (scale d) a b x y ((4*a+b-26)/4) ((b+4)/2) u v 26 4 near'
          (by omega) (by omega) (by omega) (by omega)
        right
        rw [ite_eq_left hb2, ite_eq_left haodd]
        exact ih _ _ _ _ hhigh hr hnear
    · have heven : x%2=0 := by omega
      have haeven : a%2≠1 := by omega
      obtain ⟨u,v,hr,hu,hv,hmod⟩ := grammar.2 x y (by omega) heven root
      have hb2 : b%4=2 := by omega
      have hhigh : 36*2^d ≤ u+3 := by omega
      have hnear := exceptional (scale d) a b x y ((4*a+b-14)/4) (b/2) u v 14 0 near'
        (by omega) (by omega) (by omega) (by omega)
      right
      rw [ite_eq_left hb2, ite_eq_right haeven]
      exact ih _ _ _ _ hhigh hr hnear

#print axioms first
#print axioms exceptional
#print axioms search_sound
end BB429DyadicTransport
