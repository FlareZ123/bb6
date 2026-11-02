import MediumConeGap
import ShortConeBridge
import PosEvenForm

namespace BB6.Agent1ShortCone
open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot

/-- A uniform 15q-cost exclusion for either authentic two-sector P1 root.
    OddCone is the source-complete genuine G-inverse relation. -/
theorem medium_root_even_gap
    (q b d m t k c : Nat) (root : Bool)
    (hq:1≤q)
    (hcone:OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb:8≤b) (hb4:b%4=0) (hd:d%2=1)
    (hi:inverseAt b d t=some (k,c)) (hc:c%2=0)
    (hcost:m+t+1≤15*q) :
    28*2^(16*q)<2*k+8 ∧ 2*k+8<56*2^(16*q) := by
  let u := u2 q
  have hdom:=pow16_dom q hq
  have hu:u+4*q+3=7*2^(16*q) := by dsimp [u,u2]; omega
  have hpower := inverseAt_power b d t k c hi
  have hback0 := inverseAt_exact_mass b d t k c (by omega) hb4 hd hi
  have hback:2*k+c+2*t+1=b+d := by omega
  cases root with
  | false =>
    have hm:=odd_cone_mass (6*u-2) (2*u+5) b d m (by simpa [u] using hcone)
    have hmass:b+d+2*m=8*u+3 := by omega
    have hh:=odd_cone_left_bound (6*u-2) (2*u+5) b d m (by simpa [u] using hcone)
    have hleft:4*u+8≤2^m*(b+12) := by
      have hfirst : 4*u+8≤6*u-2+12 := by omega
      exact Nat.le_trans hfirst hh
    exact medium_even_power_gap q u 3 m t b d k c hq (Or.inl rfl) hu hmass hleft hcost hb4 hd hc hpower hback
  | true =>
    have hm:=odd_cone_mass (4*u-4) (4*u+9) b d m (by simpa [u] using hcone)
    have hmass:b+d+2*m=8*u+5 := by omega
    have hh:=odd_cone_left_bound (4*u-4) (4*u+9) b d m (by simpa [u] using hcone)
    have hleft:4*u+8≤2^m*(b+12) := by
      have hfirst : 4*u+8=4*u-4+12 := by omega
      exact hfirst ▸ hh
    exact medium_even_power_gap q u 5 m t b d k c hq (Or.inr rfl) hu hmass hleft hcost hb4 hd hc hpower hback

/-- A terminal even-right source of inverse cost at most 15q cannot have
    the positive-even-right left-coordinate form of any reached P1 state. -/
theorem medium_root_even_not_power
    (q b d m t k c j : Nat) (root : Bool)
    (hq:1≤q)
    (hcone:OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb:8≤b) (hb4:b%4=0) (hd:d%2=1)
    (hi:inverseAt b d t=some (k,c)) (hc:c%2=0)
    (hcost:m+t+1≤15*q) :
    2*k+8 ≠ 14*2^j := by
  obtain ⟨hl,hr⟩ := medium_root_even_gap q b d m t k c root hq hcone hb hb4 hd hi hc hcost
  intro he
  by_cases hj:j≤16*q+1
  · have hp:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hj
    have hw:2^(16*q+1)=2*2^(16*q):=by rw [Nat.pow_succ]; omega
    omega
  · have hj2:16*q+2≤j:=by omega
    have hp:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hj2
    have hw:2^(16*q+2)=4*2^(16*q):=by rw [Nat.pow_add]; omega
    omega

/-- Authentic blank-entry reachability exclusion for short even-source leaves
    of either P1 critical feeder. The odd-only internal inverse path is exact. -/
theorem medium_root_even_not_reachable
    (q b d m t k c : Nat) (root : Bool)
    (hq:1≤q)
    (hcone:OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb:8≤b) (hb4:b%4=0) (hd:d%2=1)
    (hi:inverseAt b d t=some (k,c)) (hc:c%2=0)
    (hcost:m+t+1≤15*q) (hk:2≤k) :
    ¬ BB6.Agent1.Reach (2*k-4) (c+4) := by
  intro hr
  have hxe:(2*k-4)%2=0 := by omega
  have hyp:0<c+4 := by omega
  have hye:(c+4)%2=0 := by omega
  obtain ⟨j,hj⟩ :=
    BB6.Agent1.even_left_power_shape (2*k-4) (c+4) hr hxe hyp hye
  have heq:2*k-4+12=2*k+8 := by omega
  rw [heq] at hj
  exact (medium_root_even_not_power q b d m t k c j root hq hcone hb hb4 hd hi hc hcost) hj

#print axioms medium_root_even_gap
#print axioms medium_root_even_not_power
#print axioms medium_root_even_not_reachable
end BB6.Agent1ShortCone
