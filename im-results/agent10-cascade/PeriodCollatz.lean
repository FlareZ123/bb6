import Std

namespace CascadeCollatz

/-- The shortcut Collatz map on numerators with fixed odd denominator r. -/
def step (r n : Int) : Int :=
  if n % 2 = 0 then n / 2 else (3 * n + r) / 2

def iterate (r : Int) : Nat → Int → Int
  | 0, n => n
  | a+1, n => iterate r a (step r n)

theorem iterate_add (r : Int) (a b : Nat) (n : Int) :
    iterate r (a+b) n = iterate r b (iterate r a n) := by
  induction a generalizing n with
  | zero => simp [iterate]
  | succ a ih =>
    rw [show a+1+b=a+b+1 by omega, iterate, iterate, ih]

theorem odd_run (r m : Int) (a : Nat) (hr : r % 2 = 1)
    (hm : m % 2 = 1) :
    iterate r a ((2 : Int)^a * m - r) = (3 : Int)^a * m - r := by
  induction a generalizing m with
  | zero => simp [iterate]
  | succ a ih =>
    have he : ((2 : Int)^(a+1)*m-r) % 2 = 1 := by
      rw [Int.pow_succ]
      have h : (2:Int)^a * 2 * m - r = 2 * ((2:Int)^a*m)-r := by
        ac_rfl
      rw [h]
      omega
    have hs : step r ((2 : Int)^(a+1)*m-r) = (2 : Int)^a*(3*m)-r := by
      unfold step
      rw [if_neg (by omega : ¬ ((2 : Int)^(a+1)*m-r)%2 = 0), Int.pow_succ]
      have h : (2:Int)^a * 2 * m = 2 * ((2:Int)^a*m) := by ac_rfl
      rw [h, show (2:Int)^a*(3*m) = 3*((2:Int)^a*m) by ac_rfl]
      omega
    rw [iterate, hs, ih (3*m) (by omega)]
    rw [Int.pow_succ]
    ac_rfl

theorem block (r m : Int) (a : Nat) (hr : r % 2 = 1)
    (hm : m % 2 = 1) :
    iterate r (a+1) ((2 : Int)^a*m-r) = ((3 : Int)^a*m-r)/2 := by
  rw [iterate_add, odd_run r m a hr hm]
  have hp : (3:Int)^a % 2 = 1 := by
    induction a with
    | zero => decide
    | succ a ih => rw [Int.pow_succ, Int.mul_emod, ih]; decide
  have he : ((3:Int)^a*m-r)%2 = 0 := by
    rw [Int.sub_emod, Int.mul_emod, hp, hm]
    omega
  simp [iterate, step, he]

end CascadeCollatz

#print axioms CascadeCollatz.iterate_add
#print axioms CascadeCollatz.odd_run
#print axioms CascadeCollatz.block
