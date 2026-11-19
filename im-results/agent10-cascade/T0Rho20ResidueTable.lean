import ResetChain

namespace CascadeT0Rho20Residue

/-- For the selected rho=20 representative, the offset from
    K0 = 97*2^(a-7)-3 is 33 when 6|a and 51 otherwise. -/
def delta (a : Nat) : Nat :=
  if a % 6 = 0 then 33 else 51

def q (a : Nat) : Nat := 2 * delta a + 1

/-- A = 2^(a_actual-7) mod 81 with a_actual = a+18. -/
def A (a : Nat) : Nat := 2^(a+11) % 81

/-- C = 2^(24-7*a_actual) mod 81, using exponent reduction mod 54. -/
def C (a : Nat) : Nat := 2^((168-7*a) % 54) % 81

/-- The closed modular expression for 3*X mod 81. -/
def threeX (a : Nat) : Nat :=
  (51 + 32*A a + q a - 2*q a*C a) % 81

/-- The closed modular expression for 9*X1 mod 81. -/
def nineX1 (a : Nat) : Nat :=
  (33 + 2*A a - q a*(8*C a+5)) % 81

def expected : Nat → Nat × Nat
  | 0  => (54,27)
  | 2  => (54,0)
  | 4  => (54,54)
  | 6  => (54,27)
  | 8  => (27,54)
  | 10 => (0,0)
  | 12 => (54,27)
  | 14 => (0,27)
  | 16 => (27,27)
  | _  => (0,0)

/-- Exact nine-row modular table for the rho=20 family.
    The two entries are (3*X mod 81, 9*X1 mod 81). -/
theorem rho20_modular_table (a : Nat) (ha : a < 18) (he : a % 2 = 0) :
    (threeX a, nineX1 a) = expected a := by
  have hcases :
      a=0 ∨ a=2 ∨ a=4 ∨ a=6 ∨ a=8 ∨ a=10 ∨ a=12 ∨ a=14 ∨ a=16 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h | h
  all_goals subst a <;> decide

#print axioms rho20_modular_table

end CascadeT0Rho20Residue
