import AffineOrbitRigidity

namespace PeriodicMacro

structure Letter where
  j : Nat
  isE : Bool
  deriving Repr, DecidableEq

def scale (x : Letter) : Nat := 4^x.j

def cost (x : Letter) : Nat := if x.isE then 4 else 10

def rankCost (x : Letter) : Nat := 3*x.j + (if x.isE then 2 else 4)

/-- Exact source-independent combined pair-plus-even-F macro, expressed
in first coordinate u and half-rank r=(6u+D)/2. -/
def Step (x : Letter) (u r v s : Nat) : Prop :=
  scale x * v = u+r+cost x ∧ s=r+rankCost x

inductive Walk : List Letter → Nat → Nat → Nat → Nat → Prop where
  | nil (u r : Nat) : Walk [] u r u r
  | cons {x : Letter} {xs : List Letter} {u r v s U R : Nat}
    (h : Step x u r v s) (tail : Walk xs v s U R) :
    Walk (x::xs) u r U R

def M : List Letter → Nat
| [] => 1
| x::xs => scale x * M xs

def A : List Letter → Nat
| [] => 0
| x::xs => 1 + scale x * A xs

def B : List Letter → Nat
| [] => 0
| x::xs => cost x + scale x * (A xs * rankCost x + B xs)

def T : List Letter → Nat
| [] => 0
| x::xs => rankCost x + T xs

theorem scale_pos (x : Letter) : 0 < scale x := by
  unfold scale
  exact Nat.pow_pos (by omega)

theorem M_pos (xs : List Letter) : 0 < M xs := by
  induction xs with
  | nil => simp [M]
  | cons x xs ih =>
    simp only [M]
    exact Nat.mul_pos (scale_pos x) ih

theorem scale_ge_four (x : Letter) (hj : 0 < x.j) :
    4 ≤ scale x := by
  change 4 ≤ 4 ^ x.j
  cases hcase : x.j with
  | zero => omega
  | succ j =>
    rw [hcase] at *
    rw [Nat.pow_succ]
    have hpow : 0 < 4^j := Nat.pow_pos (by omega)
    omega

theorem M_ge_four (x : Letter) (xs : List Letter) (hj : 0 < x.j) :
    4 ≤ M (x :: xs) := by
  simp only [M]
  have hp : 1 ≤ M xs := M_pos xs
  calc
    4 ≤ scale x := scale_ge_four x hj
    _ = scale x * 1 := by simp
    _ ≤ scale x * M xs := Nat.mul_le_mul_left (scale x) hp

/-- Every finite typed word has an exact affine transfer in the source-independent
    signed pair+F model. -/
theorem transfer {xs : List Letter} {u r U R : Nat} (h : Walk xs u r U R) :
    M xs * U = u + A xs*r + B xs ∧ R = r + T xs := by
  induction h with
  | nil u r => simp [M,A,B,T]
  | @cons x xs u r v s U R hstep htail ih =>
    obtain ⟨hmp,htr⟩ := ih
    obtain ⟨hs,ht⟩ := hstep
    simp only [M,A,B,T]
    constructor
    · dsimp [Step,scale,cost,rankCost] at hs ht ⊢
      grind
    · simp only [rankCost] at ht ⊢
      omega

def PeriodOrbit (xs : List Letter) (u r : Nat → Nat) : Prop :=
  ∀ n, Walk xs (u n) (r n) (u (n+1)) (r (n+1))

theorem periodic_rank_linear (xs : List Letter) (u r : Nat → Nat)
    (h : PeriodOrbit xs u r) :
    ∀ n, r n = r 0 + n * T xs := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := (transfer (h n)).2
    rw [hs, ih]
    simp only [Nat.succ_mul]
    omega

/-- A repeated finite typed pair/F word has an exactly affine
    first-coordinate orbit in the repetition index. This is conditional
    on the explicit model Walk, not a source-TM nonhalting theorem. -/
theorem periodic_word_is_affine (xs : List Letter) (hM : 2 ≤ M xs)
    (u r : Nat → Nat) (h : PeriodOrbit xs u r) :
    ∃ s b : Int, (∀ n, (u n:Int) = s*(n:Int)+b) ∧
      ((M xs:Int)-1)*s = ((A xs*T xs):Int) := by
  have hr := periodic_rank_linear xs u r h
  let U : Nat → Int := fun n => (u n : Int)
  have hu (n : Nat) : (M xs:Int)*U (n+1) =
      U n + ((A xs*T xs):Int)*(n:Int) + ((A xs*r 0+B xs):Int) := by
    have hmp := (transfer (h n)).1
    have hrn := hr n
    have hnat : M xs * u (n+1) =
        u n + (A xs*T xs)*n + (A xs*r 0+B xs) := by
      rw [hrn] at hmp
      grind
    dsimp [U]
    exact_mod_cast hnat
  exact PeriodicRigidity.affine_orbit_rigidity (M xs) hM U
    ((A xs*T xs):Int) ((A xs*r 0+B xs):Int) hu

#print axioms transfer
#print axioms periodic_word_is_affine
end PeriodicMacro
