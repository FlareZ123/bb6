import TerminalResiduesArithmetic
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SpaceNeedleExp

def evenIdx (r : Nat) : Nat := (389 * (r/2+494)) % 500
def oddIdx (r : Nat) : Nat := (449 * ((r+331)/2)) % 500

def evenKe (n : Nat) : Nat := 12+18*n

def choose1000 (r bound : Nat) : Nat :=
  if r%2=0 then evenKe (evenIdx r + 500*bound)
  else K (oddIdx r + 500*bound)

private theorem evenResidue (r b : Nat) (hr : r < 1000) (he : r%2=0) :
    (evenKe (evenIdx r + 500*b))%1000 = r := by
  simp only [evenIdx, evenKe]
  omega

private theorem oddResidue (r b : Nat) (hr : r < 1000) (ho : r%2=1) :
    (K (oddIdx r + 500*b))%1000 = r := by
  simp only [oddIdx, K]
  omega

private theorem evenModBase : (2:Nat)^13%19=3 := by decide
private theorem evenModPeriod : (2:Nat)^18%19=1 := by decide

private theorem evenMod (n : Nat) : (2:Nat)^(evenKe n+1)%19=3 := by
  have hm (n : Nat) : (2:Nat)^(13+18*n)%19=3 := by
    induction n with
    | zero => simpa using evenModBase
    | succ n ih =>
      rw [show 13+18*(n+1)=(13+18*n)+18 by omega]
      rw [Nat.pow_add, Nat.mul_mod,ih,evenModPeriod]
  have heq : evenKe n+1=13+18*n := by simp [evenKe]; omega
  rw [heq]
  exact hm n

private def evenU (n : Nat) : Nat := ((2:Nat)^(evenKe n+1)-3)/19
def e3Q (n : Nat) : Nat := (evenU n-3)/2

private theorem evenProduct (n : Nat) :
    19*evenU n+3=(2:Nat)^(evenKe n+1) := by
  have hx := evenMod n
  have hl : 3 ≤ (2:Nat)^(evenKe n+1) := by
    have hp : 3 ≤ (2:Nat)^13 := by decide
    exact Nat.le_trans hp (Nat.pow_le_pow_right (by omega) (by simp [evenKe]))
  dsimp [evenU]
  have hmod := Nat.mod_add_div ((2:Nat)^(evenKe n+1)) 19
  omega

private theorem evenOdd (n : Nat) : evenU n%2=1 := by
  have h := evenProduct n
  have heven : (2:Nat)^(evenKe n+1)%2=0 := by
    rw [show evenKe n+1=(evenKe n)+1 by omega, Nat.pow_succ]
    omega
  omega

private theorem evenLarge (n : Nat) : evenU n ≥ 3 := by
  have h := evenProduct n
  have hl : 19*3+3 ≤ (2:Nat)^(evenKe n+1) := by
    have hp : 19*3+3 ≤ (2:Nat)^13 := by decide
    exact Nat.le_trans hp (Nat.pow_le_pow_right (by omega) (by simp [evenKe]))
  omega

private theorem e3QIdentity (n : Nat) : 2*e3Q n+3 = evenU n := by
  have ho := evenOdd n
  have hl := evenLarge n
  dsimp [e3Q]
  omega

theorem even3Equation (n : Nat) :
    (2:Nat)^(evenKe n+1)+3 = (2^4+3)*(2*e3Q n+3)+6 := by
  have hh := evenProduct n
  have hq := e3QIdentity n
  change (2:Nat)^(evenKe n+1)+3 = 19*(2*e3Q n+3)+6
  omega

/-- A complete predecessor with valuation 3 for all K=12+18n. -/
theorem even3Predecessor (n : Nat) :
    (2:Nat)^3*(2*e3Q n+3)-2+3+3*(e3Q n+1) =
      (2:Nat)^(evenKe n)-2 := by
  have h := even3Equation n
  rw [show evenKe n+1=(evenKe n)+1 by omega, Nat.pow_succ] at h
  have hpositive : 2 ≤ (2:Nat)^(evenKe n) := by
    have h2 : (2:Nat)^2 ≤ (2:Nat)^(evenKe n) :=
      Nat.pow_le_pow_right (by omega) (by simp [evenKe]; omega)
    omega
  have hsource : 2 ≤ (2:Nat)^3*(2*e3Q n+3) := by
    have hc : (2:Nat)^3=8 := by decide
    rw [hc]
    omega
  change (2:Nat)^(evenKe n)*2+3 = 19*(2*e3Q n+3)+6 at h
  have hc : (2:Nat)^3=8 := by decide
  rw [hc]
  omega

/-- Every residue modulo 1000 contains arbitrarily large terminal exponents
with an explicit exact one-step predecessor. -/
theorem thousand_predecessors (r bound : Nat) (hr : r < 1000) :
    ∃ k q v, bound ≤ k ∧ k%1000=r ∧
      ((2:Nat)^v*(2*q+3)-2+v+3*(q+1) = (2:Nat)^k-2) := by
  by_cases he : r%2=0
  · refine ⟨evenKe (evenIdx r + 500*bound),e3Q (evenIdx r + 500*bound),3,?_,?_,?_⟩
    · simp [evenKe]; omega
    · exact evenResidue r bound hr he
    · exact even3Predecessor _
  · have ho : r%2=1 := by omega
    refine ⟨K (oddIdx r + 500*bound),q (oddIdx r + 500*bound),11,?_,?_,?_⟩
    · simp [K]; omega
    · exact oddResidue r bound hr ho
    · exact predecessor _

end SpaceNeedleExp
#print axioms SpaceNeedleExp.even3Predecessor
#print axioms SpaceNeedleExp.thousand_predecessors
