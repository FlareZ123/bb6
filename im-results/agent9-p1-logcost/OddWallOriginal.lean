import OddResetOriginal
import OddWallArithmetic

namespace BB6.Agent9OddWall
open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot
open BB6.Agent1ShortCone
open BB6.Agent9OddReset

/-- A positive-depth odd inverse can meet the candidate affine wall only
after exponential prior cost. Depth>=2 requires still more cost. -/
theorem authentic_positive_depth_wall_cost
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hdodd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hcodd : c%2=1) (hk : 2 ≤ k)
    (ht : 1 ≤ t)
    (hbudget : m+t+1 < 8*2^(16*q))
    (hwall : 2*k-4 = 4*(m+t+1)+64*q+
      (if root then 12 else 16)) :
    9*2^(16*q) ≤ 2*(m+t+1) ∧
      (2≤t → 7*2^(16*q) ≤ m+t+1) := by
  have hPgrowth : 256*q ≤ 2^(8*q) := growth q hq
  have hPpow : 2^(8*q) ≤ 2^(16*q) :=
    Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
  have hP : 256*q ≤ 2^(16*q) := Nat.le_trans hPgrowth hPpow
  have hdelta : (if root then 12 else 16)=12 ∨
    (if root then 12 else 16)=16 := by
    cases root <;> simp
  have hlarge := authentic_positive_depth_odd_large_left
    q b d m t k c root hq hcone hb hb4 hdodd hi hcodd hk ht hbudget
  constructor
  · exact positive_depth_wall_cost
      q (2^(16*q)) (m+t+1) (2*k-4) (if root then 12 else 16)
      hq hP hdelta hwall hlarge.1
  · intro htdeep
    exact deeper_wall_cost
      q (2^(16*q)) (m+t+1) (2*k-4) (if root then 12 else 16)
      hq hP hdelta hwall (hlarge.2 htdeep)

#print axioms authentic_positive_depth_wall_cost
end BB6.Agent9OddWall
