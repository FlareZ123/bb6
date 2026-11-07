import S4PrefixReturn8Standalone

namespace S4PrefixNinthBase
open S4PrefixReturn8Standalone

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def prefixRunFast : Nat → List Nat → List Nat
  | 0, xs => xs
  | n+1, xs => prefixRunFast n (pp xs)

theorem prefixRun_commute_pp (n : Nat) (xs : List Nat) :
    prefixRun n (pp xs) = pp (prefixRun n xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prefixRun, ih]

theorem prefixRunFast_eq (n : Nat) : ∀ xs,
    prefixRunFast n xs = prefixRun n xs := by
  induction n with
  | zero => intro xs; rfl
  | succ n ih =>
      intro xs
      change prefixRunFast n (pp xs) = pp (prefixRun n xs)
      rw [ih (pp xs), prefixRun_commute_pp n xs]

def cycle8PeriodicStart : List Nat := cycle7 ++ [109210]
def return9Fast (v : Nat) : Nat :=
  (prefixRunFast 20480 (cycle8PeriodicStart ++ [v])).getLast!

#print axioms prefixRunFast_eq
end S4PrefixNinthBase
