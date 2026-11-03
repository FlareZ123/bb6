import Lean
import Lean.Elab.Tactic.Omega
set_option exponentiation.threshold 50000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SpaceNeedleExp

def K (n : Nat) := 3669 + 4098*n
private theorem mod_base : (2:Nat)^3670%4099=19 := by decide
private theorem period : (2:Nat)^4098%4099=1 := by decide

theorem modulus (n : Nat) : (2:Nat)^(K n+1)%4099=19 := by
  have hm (n : Nat) : (2:Nat)^(3670+4098*n)%4099=19 := by
    induction n with
    | zero => simpa using mod_base
    | succ n ih =>
      rw [show 3670+4098*(n+1)=(3670+4098*n)+4098 by omega]
      rw [Nat.pow_add, Nat.mul_mod, ih, period]
  rw [show K n+1=3670+4098*n by simp [K]; omega]
  exact hm n

private def u (n : Nat) : Nat := ((2:Nat)^(K n+1)-19)/4099
def q (n : Nat) : Nat := (u n-3)/2

private theorem u_product (n : Nat) :
    4099*(u n)+19=(2:Nat)^(K n+1) := by
  have hx := modulus n
  have hl : 19 ≤ (2:Nat)^(K n+1) := by
    have hp : 19 ≤ (2:Nat)^14 := by decide
    exact Nat.le_trans hp (Nat.pow_le_pow_right (by omega) (by simp [K]; omega))
  dsimp [u]
  have hmod := Nat.mod_add_div ((2:Nat)^(K n+1)) 4099
  omega

private theorem u_odd (n : Nat) : u n % 2 = 1 := by
  have h := u_product n
  have heven : (2:Nat)^(K n+1)%2=0 := by
    rw [show K n+1=(K n)+1 by omega, Nat.pow_succ]
    omega
  omega

private theorem u_large (n : Nat) : u n ≥ 3 := by
  have h := u_product n
  have hl : 4099*3+19 ≤ (2:Nat)^(K n+1) := by
    have hp : 4099*3+19 ≤ (2:Nat)^14 := by decide
    exact Nat.le_trans hp (Nat.pow_le_pow_right (by omega) (by simp [K]; omega))
  omega

private theorem q_identity (n : Nat) : 2*q n+3 = u n := by
  have ho := u_odd n
  have hl := u_large n
  dsimp [q]
  omega

theorem equation (n : Nat) :
    (2:Nat)^(K n+1)+3 = (2^12+3)*(2*q n+3)+22 := by
  have hh := u_product n
  have hq := q_identity n
  change (2:Nat)^(K n+1)+3 = 4099*(2*q n+3)+22
  omega

/-- A complete one-step predecessor of the putative terminal height K n,
    under the exact published one-counter oddTower transition. -/
theorem predecessor (n : Nat) :
    (2:Nat)^11*(2*q n+3)-2+11+3*(q n+1) = (2:Nat)^(K n)-2 := by
  have h := equation n
  rw [show K n+1=(K n)+1 by omega, Nat.pow_succ] at h
  have hpositive : 2 ≤ (2:Nat)^(K n) := by
    have h2 : (2:Nat)^2 ≤ (2:Nat)^(K n) :=
      Nat.pow_le_pow_right (by omega) (by simp [K]; omega)
    omega
  have hsource : 2 ≤ (2:Nat)^11 * (2*q n+3) := by
    have hc : (2:Nat)^11=2048 := by decide
    rw [hc]
    omega
  change (2:Nat)^(K n)*2+3 = 4099*(2*q n+3)+22 at h
  have hc : (2:Nat)^11=2048 := by decide
  rw [hc]
  omega

/-- A second infinite source family: terminal exponents are positive
multiples of four, and have immediate predecessors with valuation zero. -/
def evenK (n : Nat) := 4*(n+1)

theorem even_mod (n : Nat) : (2:Nat)^(evenK n)%5=1 := by
  have h (n : Nat) : (2:Nat)^(4*(n+1))%5=1 := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [show 4*(n+1+1)=4*(n+1)+4 by omega]
      rw [Nat.pow_add,Nat.mul_mod,ih]
  exact h n

def evenQ (n : Nat) : Nat := ((2:Nat)^(evenK n)-6)/5

theorem even_product (n : Nat) : 5*evenQ n+6 = (2:Nat)^(evenK n) := by
  have hm := even_mod n
  have hp : 6 ≤ (2:Nat)^(evenK n) := by
    have hh : (2:Nat)^4 ≤ (2:Nat)^(evenK n) :=
      Nat.pow_le_pow_right (by omega) (by simp [evenK]; omega)
    omega
  have hmod := Nat.mod_add_div ((2:Nat)^(evenK n)) 5
  dsimp [evenQ]
  omega

theorem even_predecessor (n : Nat) :
    2*evenQ n+1+3*(evenQ n+1) = (2:Nat)^(evenK n)-2 := by
  have h := even_product n
  omega

/-- The complete concrete arithmetic meaning of an immediate positive
successor of the Space Needle oddTower class, with v=0 or v=11. -/
def HasPredecessor (k : Nat) : Prop :=
  (∃ q, 2*q+1+3*(q+1) = (2:Nat)^k-2) ∨
  (∃ q, (2:Nat)^11*(2*q+3)-2+11+3*(q+1) = (2:Nat)^k-2)

theorem even_has_predecessor (n : Nat) : HasPredecessor (evenK n) := by
  exact Or.inl ⟨evenQ n, even_predecessor n⟩

theorem odd_has_predecessor (n : Nat) : HasPredecessor (K n) := by
  exact Or.inr ⟨q n, predecessor n⟩

/-- The first five of each parity family fill every residue modulo ten.
A stride of five in n preserves the residue and exceeds any lower bound. -/
def baseIndex (r : Nat) : Nat :=
  if r=0 then 4 else if r=2 then 2 else if r=4 then 0 else
  if r=6 then 3 else if r=8 then 1 else if r=1 then 4 else
  if r=3 then 3 else if r=5 then 2 else if r=7 then 1 else 0

def selectK (r bound : Nat) : Nat :=
  if r%2=0 then evenK (baseIndex r+5*bound) else K (baseIndex r+5*bound)

theorem selectK_correct (r bound : Nat) (hr : r < 10) :
    bound ≤ selectK r bound ∧ selectK r bound % 10=r ∧
    HasPredecessor (selectK r bound) := by
  have witness : HasPredecessor (selectK r bound) := by
    unfold selectK
    split
    · exact even_has_predecessor _
    · exact odd_has_predecessor _
  have hb : bound ≤ selectK r bound := by
    unfold selectK
    split
    · simp [evenK]
      omega
    · simp [K]
      omega
  refine ⟨hb, ?_, witness⟩
  have hcases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨
    r=5 ∨ r=6 ∨ r=7 ∨ r=8 ∨ r=9 := by omega
  rcases hcases with h|h|h|h|h|h|h|h|h|h <;> subst r <;>
    simp [selectK, baseIndex, evenK, K] <;> omega

end SpaceNeedleExp
#print axioms SpaceNeedleExp.modulus
#print axioms SpaceNeedleExp.equation
#print axioms SpaceNeedleExp.predecessor
#print axioms SpaceNeedleExp.selectK_correct
