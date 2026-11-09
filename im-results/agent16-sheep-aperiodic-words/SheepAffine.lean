import Std
namespace SheepAffine

private theorem base_affine (A H R D a u v : Nat)
    (he : D*u + 2*a = R*v + 3) :
    (A*R)*(1+H*v)+(A*H)*3 =
      (H*D)*(A*u)+(A*R)+(A*H)*(2*a) := by
  calc
    _ = (A*R) + (A*H)*(R*v+3) := by
      simp only [Nat.mul_add, Nat.mul_one]
      ac_rfl
    _ = (A*R) + (A*H)*(D*u+2*a) := by rw [he]
    _ = (H*D)*(A*u)+(A*R)+(A*H)*(2*a) := by
      simp only [Nat.mul_add]
      ac_rfl

def scale (a h : Nat) : Nat := 2^a * 2^(h+1)
def factor (a h : Nat) : Nat := 3^h * (2^(a+1)+1)
def positiveOffset (a h : Nat) : Nat := scale a h + (2^a*3^h)*(2*a)
def negativeOffset (a h : Nat) : Nat := (2^a*3^h)*3

def Edge (a h x y : Nat) : Prop :=
  scale a h * y + negativeOffset a h = factor a h * x + positiveOffset a h

theorem original_generic_algebra (a h u v : Nat)
    (he : (2^(a+1)+1)*u+2*a=2^(h+1)*v+3) :
    Edge a h (2^a*u) (1+3^h*v) := by
  simpa [Edge, scale, factor, positiveOffset, negativeOffset, Nat.add_assoc] using
    (base_affine (2^a) (3^h) (2^(h+1)) (2^(a+1)+1) a u v he)

#print axioms original_generic_algebra
end SheepAffine

namespace SheepAffine

structure Params where
  L : Nat
  N : Nat
  P : Nat
  Q : Nat

abbrev Holds (p : Params) (x y : Nat) : Prop := p.L*y+p.Q=p.N*x+p.P

def compose (p q : Params) : Params :=
  { L := p.L*q.L
    N := p.N*q.N
    P := q.N*p.P+p.L*q.P
    Q := p.L*q.Q+q.N*p.Q }

theorem compose_holds (p q : Params) (x y z : Nat)
    (h1 : Holds p x y) (h2 : Holds q y z) :
    Holds (compose p q) x z := by
  have h1m := congrArg (fun t : Nat => q.N*t) h1
  have h2m := congrArg (fun t : Nat => p.L*t) h2
  simp only [Nat.mul_add] at h1m h2m
  have h1' : (p.L*q.N)*y+q.N*p.Q=(p.N*q.N)*x+q.N*p.P := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h1m
  have h2' : (p.L*q.L)*z+p.L*q.Q=(p.L*q.N)*y+p.L*q.P := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h2m
  dsimp [Holds, compose]
  omega

#print axioms compose_holds
end SheepAffine

namespace SheepAffine

theorem holds_to_int_affine (p : Params) (x y : Nat) (h : Holds p x y) :
    (p.L:Int)*y=(p.N:Int)*x+((p.P:Int)-(p.Q:Int)) := by
  have hInt := congrArg (fun t : Nat => (t:Int)) h
  simp only [Int.natCast_add, Int.natCast_mul] at hInt
  omega

#print axioms holds_to_int_affine
end SheepAffine

namespace SheepAffine

def branchParams (p : Nat × Nat) : Params :=
  { L := scale p.1 p.2
    N := factor p.1 p.2
    P := positiveOffset p.1 p.2
    Q := negativeOffset p.1 p.2 }

def wordParams : List (Nat × Nat) → Params
  | [] => ⟨1,1,0,0⟩
  | b::bs => compose (branchParams b) (wordParams bs)

def wordCost : List (Nat × Nat) → Nat
  | [] => 0
  | b::bs => b.1 + b.2 + 1 + wordCost bs

/-- Physical one-block interpretation is supplied by `original_generic_algebra`. -/
def WordPath : List (Nat × Nat) → Nat → Nat → Prop
  | [], x, y => x = y
  | b::bs, x, y => ∃ z, Holds (branchParams b) x z ∧ WordPath bs z y

theorem word_path_holds (w : List (Nat × Nat)) (x y : Nat)
    (h : WordPath w x y) : Holds (wordParams w) x y := by
  induction w generalizing x y with
  | nil =>
      dsimp [WordPath] at h
      subst y
      simp [wordParams,Holds]
  | cons b bs ih =>
      obtain ⟨z,hb,ht⟩ := h
      exact compose_holds _ _ x z y hb (ih z y ht)

private theorem two_coprime_odd (n : Nat) (h : n%2=1) : Nat.Coprime 2 n := by
  change Nat.gcd 2 n=1
  rw [Nat.gcd_add_one]
  simp [h]

private theorem factor_odd (a h : Nat) : (factor a h)%2=1 := by
  have h3 : (3^h)%2=1 := by rw [Nat.pow_mod]; simp
  have h2 : (2^(a+1))%2=0 := by rw [Nat.pow_mod]; simp
  simp only [factor]
  rw [Nat.mul_mod, Nat.add_mod]
  simp [h3,h2]

theorem word_scale (w : List (Nat × Nat)) :
    (wordParams w).L=2^(wordCost w) := by
  induction w with
  | nil => simp [wordParams,wordCost]
  | cons b bs ih =>
      simp only [wordParams, compose, branchParams, wordCost]
      rw [ih]
      simp only [scale, ← Nat.pow_add]
      congr 1

theorem word_factor_odd (w : List (Nat × Nat)) :
    (wordParams w).N%2=1 := by
  induction w with
  | nil => simp [wordParams]
  | cons b bs ih =>
      simp only [wordParams, compose, branchParams]
      rw [Nat.mul_mod]
      simp [factor_odd, ih]

theorem word_coprime (w : List (Nat × Nat)) :
    (wordParams w).L.Coprime (wordParams w).N := by
  rw [word_scale]
  exact (two_coprime_odd _ (word_factor_odd w)).pow_left (wordCost w)

theorem nonempty_word_scale_gt_one {w : List (Nat × Nat)}
    (hn : w ≠ []) : 1 < (wordParams w).L := by
  rw [word_scale]
  have hc : wordCost w ≠ 0 := by
    cases w with
    | nil => contradiction
    | cons b bs => simp only [wordCost]; omega
  exact Nat.one_lt_pow hc (by decide)

#print axioms word_path_holds
#print axioms word_scale
#print axioms word_factor_odd
#print axioms word_coprime
#print axioms nonempty_word_scale_gt_one
end SheepAffine
