import LowCostPower
import UniversalSmallLeft

namespace BB6.Agent45LowCost
open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot

/-- Source-connected low-cost dichotomy on the genuine two-feeder inverse
cone: any blank-reachable positive-even terminal feeder forces the stated
single affine predecessor line, and its final G inverse depth is one. -/
theorem source_low_cost_even_target
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : c%2=0) (hk : 2≤k)
    (hshort : m ≤ 7*2^(16*q))
    (hr : BB6.Agent1.Reach (2*k-4) (c+4)) :
    t=1 ∧ (if root then b=4*m+64*q+12 else b=4*m+64*q+16) := by
  let u := u2 q
  have hdom := pow16_dom q hq
  have hu : u+4*q+3=7*2^(16*q) := by
    dsimp [u,u2]
    omega
  have hxe : (2*k-4)%2=0 := by omega
  have hyp : 0<c+4 := by omega
  have hye : (c+4)%2=0 := by omega
  obtain ⟨j, hj0⟩ :=
    BB6.Agent1.even_left_power_shape (2*k-4) (c+4) hr hxe hyp hye
  have hpower : 2*k+8=14*2^j := by omega
  have hinverse := inverseAt_power b d t k c hi
  have hcost0 := inverseAt_exact_mass b d t k c (by omega) hb4 hd hi
  have hcost : 2*k+c+2*t+1=b+d := by omega
  cases root with
  | false =>
    have hm := odd_cone_mass (6*u-2) (2*u+5) b d m
      (by simpa [u] using hcone)
    have hmass : b+d+2*m=8*u+3 := by omega
    have hfull : b+d+2*m+32*q+24=56*2^(16*q)+3 := by omega
    have hdepth := BB6.Agent1Bottleneck.inverse_depth_le
      q u b d m t c 3 hu (Or.inl rfl) hmass hinverse
    obtain ⟨_,ht,_,hl⟩ :=
      low_cost_power_leaf_shape q b d m t k c j 3 hq (Or.inl rfl)
        hfull hb hb4 hd hc hinverse hdepth hcost hpower hshort
    simpa using (show t=1 ∧ b=4*m+64*q+16 from ⟨ht,hl rfl⟩)
  | true =>
    have hm := odd_cone_mass (4*u-4) (4*u+9) b d m
      (by simpa [u] using hcone)
    have hmass : b+d+2*m=8*u+5 := by omega
    have hfull : b+d+2*m+32*q+24=56*2^(16*q)+5 := by omega
    have hdepth := BB6.Agent1Bottleneck.inverse_depth_le
      q u b d m t c 5 hu (Or.inr rfl) hmass hinverse
    obtain ⟨_,ht,hl,_⟩ :=
      low_cost_power_leaf_shape q b d m t k c j 5 hq (Or.inr rfl)
        hfull hb hb4 hd hc hinverse hdepth hcost hpower hshort
    simpa using (show t=1 ∧ b=4*m+64*q+12 from ⟨ht,hl rfl⟩)

#print axioms BB6.Agent45LowCost.source_low_cost_even_target
end BB6.Agent45LowCost
