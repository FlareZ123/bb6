import MediumConeReach
import InverseIff
namespace BB6.Agent1Bottleneck

/-- Exact unbounded inverse-cone obstruction. Every even source with the
blank-reachable power shape forces its immediately preceding odd hub to have
small left counter relative to the accumulated inverse cost. -/
theorem small_left_of_power_leaf
    (q u b d m t k c j : Nat) (e : Nat)
    (hq : 1 ≤ q)
    (he : e = 3 ∨ e = 5)
    (hu : u + 4*q + 3 = 7 * 2^(16*q))
    (hmass : b+d+2*m = 8*u+e)
    (hb4 : b % 4 = 0)
    (hd : d % 2 = 1)
    (hc : c % 2 = 0)
    (hinverse : d+b/2+3 = 2^t*(c+3))
    (hcost : 2*k+c+2*t+1 = b+d)
    (hpower : 2*k+8 = 14*2^j) :
    b ≤ 64*q+4*m+8*t+8 := by
  have ht : 1 ≤ t := by
    have hn : t ≠ 0 := by
      intro hzero
      subst t
      simp only [Nat.pow_zero, Nat.one_mul] at hinverse
      omega
    omega
  have htwopow : 2 ≤ 2^t := by
    have hp : 2^1 ≤ 2^t := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) ht
    simpa using hp
  have hhalf : 2*(c+3) ≤ d+b/2+3 := by
    calc
      2*(c+3) ≤ 2^t*(c+3) := Nat.mul_le_mul_right (c+3) htwopow
      _ = d+b/2+3 := hinverse.symm
  have hscaled : 8*u+32*q+24 = 56*2^(16*q) := by omega
  have hupper : 14*2^j < 56*2^(16*q) := by
    rcases he with he | he <;> omega
  have hj : j ≤ 16*q+1 := by
    by_cases hh : j ≤ 16*q+1
    · exact hh
    have hge : 16*q+2 ≤ j := by omega
    have hp : 2^(16*q+2) ≤ 2^j := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hge
    have hs : 2^(16*q+2) = 4 * 2^(16*q) := by
      rw [Nat.pow_add]
      have hp2 : (2:Nat)^2=4 := by decide
      rw [hp2]
      omega
    omega
  have hjs : 2^j ≤ 2^(16*q+1) := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hj
  have hs : 2^(16*q+1) = 2*2^(16*q) := by rw [Nat.pow_succ]; omega
  have hbound : 2*k+8 ≤ 28*2^(16*q) := by omega
  rcases he with he | he <;> omega

/-- Uniform inverseAt depth restriction at scale 2^(16q), independent
of the number of prior G-inverse edges. -/
theorem inverse_depth_le
    (q u b d m t c e : Nat)
    (hu : u+4*q+3=7*2^(16*q))
    (he : e=3 ∨ e=5)
    (hmass : b+d+2*m=8*u+e)
    (hinverse : d+b/2+3=2^t*(c+3)) :
    t ≤ 16*q+4 := by
  have hscaled : 8*u+32*q+24=56*2^(16*q) := by omega
  have hs : d+b/2+3 <56*2^(16*q) := by
    rcases he with he | he <;> omega
  have hp : 2^t*(c+3) <56*2^(16*q) := by omega
  by_cases htt : t ≤ 16*q+4
  · exact htt
  have htg : 16*q+5 ≤ t := by omega
  have hh : 2^(16*q+5) ≤ 2^t := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) htg
  have heq : 2^(16*q+5) = 32*2^(16*q) := by
    rw [Nat.pow_add]
    have hz : (2:Nat)^5=32 := by decide
    rw [hz]
    omega
  have hc : 3 ≤ c+3 := by omega
  have hmul : 2^t*3 ≤ 2^t*(c+3) := Nat.mul_le_mul_left _ hc
  omega

/-- The power-compatible leaf's left predecessor is bounded using only q
and the total odd-inverse path cost m, with no bounded-depth hypothesis. -/
theorem small_left_of_power_leaf_strong
    (q u b d m t k c j : Nat) (e : Nat)
    (hq : 1 ≤ q)
    (he : e = 3 ∨ e = 5)
    (hu : u + 4*q + 3 = 7 * 2^(16*q))
    (hmass : b+d+2*m = 8*u+e)
    (hb4 : b % 4 = 0)
    (hd : d % 2 = 1)
    (hc : c % 2 = 0)
    (hinverse : d+b/2+3 = 2^t*(c+3))
    (hcost : 2*k+c+2*t+1 = b+d)
    (hpower : 2*k+8 = 14*2^j) :
    b ≤ 4*m+192*q+40 := by
  have hb := small_left_of_power_leaf q u b d m t k c j e hq he hu hmass hb4 hd hc hinverse hcost hpower
  have ht := inverse_depth_le q u b d m t c e hu he hmass hinverse
  omega

open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot
open BB6.Agent1ShortCone

/-- Genuine-source all-depth necessary condition. Any even-counter input to
an odd inverse cone of either authentic P1 critical feeder that could have
been visited from blank must originate at a left-small odd hub. No cost
bound or inverse-chain depth bound is required. -/
theorem reachable_even_terminal_small_left
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : c%2=0) (hk : 2 ≤ k)
    (hr : BB6.Agent1.Reach (2*k-4) (c+4)) :
    b ≤ 4*m+192*q+40 := by
  let u := u2 q
  have hdom := pow16_dom q hq
  have hu : u+4*q+3=7*2^(16*q) := by dsimp [u,u2]; omega
  have heven : (2*k-4)%2=0 := by omega
  have hpositive : 0<c+4 := by omega
  have hright : (c+4)%2=0 := by omega
  obtain ⟨j, hj⟩ := BB6.Agent1.even_left_power_shape
     (2*k-4) (c+4) hr heven hpositive hright
  have hpower : 2*k+8=14*2^j := by omega
  have hinverse := inverseAt_power b d t k c hi
  have hcost0 := inverseAt_exact_mass b d t k c (by omega) hb4 hd hi
  have hcost : 2*k+c+2*t+1=b+d := by omega
  cases root with
  | false =>
    have hm:=odd_cone_mass (6*u-2) (2*u+5) b d m (by simpa [u] using hcone)
    have hmass:b+d+2*m=8*u+3 := by omega
    exact small_left_of_power_leaf_strong q u b d m t k c j 3 hq (Or.inl rfl) hu hmass hb4 hd hc hinverse hcost hpower
  | true =>
    have hm:=odd_cone_mass (4*u-4) (4*u+9) b d m (by simpa [u] using hcone)
    have hmass:b+d+2*m=8*u+5 := by omega
    exact small_left_of_power_leaf_strong q u b d m t k c j 5 hq (Or.inr rfl) hu hmass hb4 hd hc hinverse hcost hpower

#print axioms small_left_of_power_leaf
#print axioms inverse_depth_le
#print axioms small_left_of_power_leaf_strong
#print axioms reachable_even_terminal_small_left
end BB6.Agent1Bottleneck
