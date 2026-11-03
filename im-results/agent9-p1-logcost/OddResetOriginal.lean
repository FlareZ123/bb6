import CostOriginal
import OddResetArithmetic
namespace BB6.Agent9OddReset
open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot
open BB6.Agent1ShortCone
open BB6.Agent1Bottleneck

theorem authentic_positive_depth_odd_large_left
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hdodd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hcodd : c%2=1) (hk : 2 ≤ k)
    (ht : 1 ≤ t)
    (hbudget : m+t+1 < 8*2^(16*q)) :
    19*2^(16*q) ≤ 2*k-4 ∧
      (2≤t → 29*2^(16*q) ≤ 2*k-4) := by
  let u := u2 q
  let e := if root then 5 else 3
  have hdom := pow16_dom q hq
  have hu : u+4*q+3=7*2^(16*q) := by dsimp [u,u2]; omega
  have he : e=3 ∨ e=5 := by
    cases root <;> simp [e]
  have hmass : b+d+2*m=8*u+e := by
    cases root with
    | false =>
      have hh := odd_cone_mass (6*u-2) (2*u+5) b d m
        (by simpa [u] using hcone)
      dsimp [e]
      omega
    | true =>
      have hh := odd_cone_mass (4*u-4) (4*u+9) b d m
        (by simpa [u] using hcone)
      dsimp [e]
      omega
  have hPsmall : 256*q ≤ 2^(8*q) := growth q hq
  have hPpow : 2^(8*q) ≤ 2^(16*q) :=
    Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
  have hP : 256*q ≤ 2^(16*q) := Nat.le_trans hPsmall hPpow
  have hinverse := inverseAt_power b d t k c hi
  have hmassInverse := inverseAt_odd_cost b d t k c
    (by omega) hb4 hdodd hi hcodd
  have hcost : 2*k+c+2*t+2=b+d := by omega
  have htbound := inverse_depth_le q u b d m t c e hu he hmass hinverse
  constructor
  · exact positive_depth_odd_has_large_left
      q u e b d m t k c hq he hu hmass hinverse hcost hk ht
      htbound hbudget hP
  · intro htdeep
    exact deeper_odd_has_large_left
      q u e b d m t k c hq he hu hmass hinverse hcost hk htdeep
      htbound hbudget hP

/-- If a positive-depth authentic odd inverse lands on either exact
    low-cost affine wall, the accumulated cost is already exponential. -/
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
    (hwall : 2*k-4=4*(m+t+1)+64*q+
      (if root then 12 else 16)) :
    9*2^(16*q) ≤ 2*(m+t+1) ∧
      (2≤t → 7*2^(16*q) ≤ m+t+1) := by
  have hsource := authentic_positive_depth_odd_large_left
    q b d m t k c root hq hcone hb hb4 hdodd hi hcodd hk ht hbudget
  have hPgrowth : 256*q ≤ 2^(8*q) := growth q hq
  have hPpow : 2^(8*q) ≤ 2^(16*q) :=
    Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
  have hP : 256*q ≤ 2^(16*q) := Nat.le_trans hPgrowth hPpow
  have hdelta : (if root then 12 else 16)=12 ∨
      (if root then 12 else 16)=16 := by
    cases root <;> simp
  constructor
  · rcases hdelta with h | h <;> omega
  · intro htdeep
    have hlarge := hsource.2 htdeep
    rcases hdelta with h | h <;> omega

#print axioms authentic_positive_depth_wall_cost

#print axioms authentic_positive_depth_odd_large_left
end BB6.Agent9OddReset
