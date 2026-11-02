import Std
namespace BB6.BTrace

def G (z : Nat) : Nat := 3*(z/2)+4+5*(z%2)
def iterG : Nat → Nat → Nat
  | 0,z => z
  | n+1,z => iterG n (G z)

theorem iterG_add (m n z : Nat) :
    iterG (m+n) z = iterG n (iterG m z) := by
  induction m generalizing z with
  | zero => simp [iterG]
  | succ m ih =>
      simpa only [Nat.succ_add,iterG] using (ih (G z))

#print axioms iterG_add
end BB6.BTrace
