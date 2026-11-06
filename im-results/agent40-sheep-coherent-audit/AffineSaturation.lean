import Std

/-!
The independent arithmetic kernel of the universal generic Sheep dyadic
diameter theorem.  An inverse gate has an affine slope divisible by 2^cost.
These theorems do not import or claim to prove the original inverse map,
word uniqueness, quotient edge realization, or blank-orbit reachability.
-/

namespace SheepDiameter

structure Gate where
  cost : Nat
  bias : Nat
  factor : Nat

def evalGate (g : Gate) (x : Nat) : Nat := g.bias + 2^g.cost * g.factor*x

def evalWord : List Gate → Nat → Nat
  | [], x => x
  | g::gs, x => evalGate g (evalWord gs x)

def cost : List Gate → Nat
  | [] => 0
  | g::gs => g.cost + cost gs

def factor : List Gate → Nat
  | [] => 1
  | g::gs => g.factor * factor gs

theorem affine_shift (gs : List Gate) (x d : Nat) :
    evalWord gs (x+d) = evalWord gs x + 2^(cost gs)*factor gs*d := by
  induction gs with
  | nil => simp [evalWord, cost, factor]
  | cons g gs ih =>
    simp only [evalWord, cost, factor, evalGate]
    rw [ih, Nat.pow_add]
    simp only [Nat.mul_add]
    ac_rfl

theorem even_saturation (gs : List Gate) (p : Nat)
    (hp : p ≤ cost gs + 1) (s t : Nat) :
    evalWord gs (2*s) % (2^p) = evalWord gs (2*t) % (2^p) := by
  have hdiv (z : Nat) : 2^p ∣ 2^(cost gs)*factor gs*(2*z) := by
    apply Nat.dvd_trans (Nat.pow_dvd_pow 2 hp)
    refine ⟨factor gs*z, ?_⟩
    rw [Nat.pow_add]
    simp only [Nat.pow_one]
    ac_rfl
  have hzero (z : Nat) : evalWord gs (2*z) % (2^p) = evalWord gs 0 % (2^p) := by
    have h := affine_shift gs 0 (2*z)
    simp only [Nat.zero_add] at h
    rw [h, Nat.add_mod, Nat.mod_eq_zero_of_dvd (hdiv z)]
    simp
  rw [hzero s, hzero t]

#print axioms affine_shift
#print axioms even_saturation
end SheepDiameter
