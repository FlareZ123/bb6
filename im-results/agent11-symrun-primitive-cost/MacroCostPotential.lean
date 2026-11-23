import Mathlib

/-!
# Quadratic exact-cost potentials for F424/F412 accelerated SymRun macros

The potentials are integer-valued because they may contain negative quadratic
terms. Each fixed proof-block's candidate primitive cost is a discrete
potential drop; telescoping over arbitrarily many iterations yields the
entire quadratic accelerated macro cost without a finite sum.

**Scope:** algebraic equalities only. The fixed-block cost/source-machine
correspondence is a separate obligation, see README.
-/

namespace BB6.Agent11.SymRunPotentials

def a424 (m k : ℤ) : ℤ := -70 * m^2 + 16 * k^2 + 368 * k
def a412 (m k : ℤ) : ℤ := -62 * m^2 + 14 * k^2 + 332 * k

def c424 (p k : ℤ) : ℤ := 38 * p^2 - 16 * k^2 + 168 * p
def c412 (p k : ℤ) : ℤ := 34 * p^2 - 14 * k^2 + 152 * p

/-- c is the macro-offset 506/436/354/284 or 458/396/322/260,
    depending on the source machine and separator pair. -/
def b424 (c p m k : ℤ) : ℤ :=
  -38 * p^2 + 70 * m^2 + 16 * k^2 + (c + 12) * m
def b412 (c p m k : ℤ) : ℤ :=
  -34 * p^2 + 62 * m^2 + 14 * k^2 + (c + 12) * m

/-- Source shape: stateA(m,k+1,d+6) → stateA(m+1,k,d). -/
theorem a424_drop (m k : ℤ) :
    a424 m (k+1) - a424 (m+1) k = 140*m+32*k+454 := by
  simp only [a424]
  ring

theorem a412_drop (m k : ℤ) :
    a412 m (k+1) - a412 (m+1) k = 124*m+28*k+408 := by
  simp only [a412]
  ring

/-- Source shape: stateC(p+3,k+1,d) → stateC(p+2,k+3,d+2). -/
theorem c424_drop (p k : ℤ) :
    c424 (p+3) (k+1) - c424 (p+2) (k+3) =
      76*p+64*k+486 := by
  simp only [c424]
  ring

theorem c412_drop (p k : ℤ) :
    c412 (p+3) (k+1) - c412 (p+2) (k+3) =
      68*p+56*k+434 := by
  simp only [c412]
  ring

/-- Source shape:
    stateB(p+1,m+2,k+1,d) → stateB(p+3,m+1,k,d+4).
    The block constant is c+542 for F424 and c+484 for F412. -/
theorem b424_drop (c p m k : ℤ) :
    b424 c (p+1) (m+2) (k+1) -
      b424 c (p+3) (m+1) k =
        152*p+140*m+32*k+(c+542) := by
  simp only [b424]
  ring

theorem b412_drop (c p m k : ℤ) :
    b412 c (p+1) (m+2) (k+1) -
      b412 c (p+3) (m+1) k =
        136*p+124*m+28*k+(c+484) := by
  simp only [b412]
  ring

/-- Full A macro: 46-step prelude followed by m copies of the 66-step
    block, i.e. n=m+1. The entering B1 repetition is K=k+n. -/
theorem a424_macro (m k : ℤ) :
    32*(k+m)+314 + (a424 0 (k+m) - a424 m k) =
      (m+1)*(32*(k+m+1)+54*(m+1)+228) := by
  simp only [a424]
  ring

theorem a412_macro (m k : ℤ) :
    28*(k+m)+284 + (a412 0 (k+m) - a412 m k) =
      (m+1)*(28*(k+m+1)+48*(m+1)+208) := by
  simp only [a412]
  ring

/-- Full C macro: n copies of the 46-step block, entering
    P=n+2 and K=k+1, exiting P=2 and K=k+1+2n. -/
theorem c424_macro (n k : ℤ) :
    c424 (n+2) (k+1) - c424 2 (k+1+2*n) =
      n*(102*n+64*(k+1)+320) := by
  simp only [c424]
  ring

theorem c412_macro (n k : ℤ) :
    c412 (n+2) (k+1) - c412 2 (k+1+2*n) =
      n*(90*n+56*(k+1)+288) := by
  simp only [c412]
  ring

/-- Full B macro: n iterations, P=p+2 and K=k+n at entry;
    the separator offset c is preserved throughout. -/
theorem b424_macro (n p k c : ℤ) :
    b424 c (p+1) (n+1) (k+n) -
      b424 c (p+1+2*n) 1 k =
        n*(206*n+152*(p+2)+32*(k+n)+c) := by
  simp only [b424]
  ring

theorem b412_macro (n p k c : ℤ) :
    b412 c (p+1) (n+1) (k+n) -
      b412 c (p+1+2*n) 1 k =
        n*(184*n+136*(p+2)+28*(k+n)+c) := by
  simp only [b412]
  ring

#print axioms a424_drop
#print axioms a412_drop
#print axioms c424_drop
#print axioms c412_drop
#print axioms b424_drop
#print axioms b412_drop
#print axioms a424_macro
#print axioms a412_macro
#print axioms c424_macro
#print axioms c412_macro
#print axioms b424_macro
#print axioms b412_macro

end BB6.Agent11.SymRunPotentials
