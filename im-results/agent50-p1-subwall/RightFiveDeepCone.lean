import RightFiveThreeSource
import RightFiveDefectStep

namespace BB6.Agent50DeepCone
open BB6.Agent1UpperTail BB6.Agent1Quarter BB6.Agent28
open BB6.Agent50Defect BB6.Agent50RightFiveTwo

/-- Exact original inverse steps, restricted to t>=2 at every edge. -/
inductive DeepCone (b0 d0 : Nat) : Nat → Nat → Nat → Prop where
  | root : DeepCone b0 d0 b0 d0 0
  | parent (b d m t k c : Nat)
      (hprev : DeepCone b0 d0 b d m)
      (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
      (hi : BB6.Agent47P1.inverseAt b d t=some (k,c))
      (hk : 2≤k) (hc : c%2=1) (ht:2≤t) :
      DeepCone b0 d0 (2*k-4) (c+4) (m+t+1)

/-- The filtered grammar embeds into the original CountCone, with an exact
count of one positive-depth inverseAt transition per edge. -/
theorem deep_cone_to_counted
    (b0 d0 b d m : Nat) (h : DeepCone b0 d0 b d m) :
    ∃ z, CountCone b0 d0 b d m z := by
  induction h with
  | root => exact ⟨0, CountCone.root⟩
  | parent b d m t k c hp hb hb4 hd hi hk hc ht ih =>
    obtain ⟨z,hz⟩ := ih
    have hnonzero : t≠0 := by omega
    refine ⟨z+1, ?_⟩
    simpa [hnonzero] using
      (CountCone.parent b d m z t k c hz hb hb4 hd hi hk hc)

/-- Exact original mass and a strict twelve-power fixed-point barrier along
every source-valid history composed exclusively of inverse depths >=2. -/
theorem deep_cone_mass_above
    (n b d m : Nat) (hn : 14≤n)
    (h : DeepCone (14*2^n-2*n-16) 3 b d m) :
    b+d+2*m+2*n+13=14*2^n ∧
    12*2^n < b+4*m+4*n+20 := by
  induction h with
  | root =>
    have hp : 100*n≤2^n := hundred_mul_le_pow n hn
    omega
  | parent b d m t k c hp hb hb4 hd hi hk hc ht ih =>
    have hInv := (inverseAt_iff_power_mass b d t k c (by omega) hb4 hd).mp hi
    have hOdd : c%2=1 := hc
    have hmassNext :
        (2*k-4)+(c+4)+2*(m+t+1)+2*n+13=14*2^n := by
      omega
    exact ⟨hmassNext,high_depth_preserves_above_twelve n b d m t k c hn
      ih.1 hb4 hInv.1 (by omega) hk ht ih.2⟩

/-- A genuine all-high-depth source inverse history ending at right counter
five must exceed the 5/2-exponential inverse cost cap. This conclusion has
no bound on the positive reset count, word length, or inverse depths. -/
theorem deep_cone_right_five_exceeds_mid_cost
    (n b m : Nat) (hn : 14≤n)
    (h : DeepCone (14*2^n-2*n-16) 3 b 5 m) :
    5*2^n < 2*m+n+2 := by
  by_cases hcost : 5*2^n < 2*m+n+2
  · exact hcost
  · exfalso
    have hbudgetLe : 2*m+n+2≤5*2^n := by omega
    cases h with
    | parent B D R t k c hprev hb hb4 hd hi hk hc ht =>
      have hbefore := deep_cone_mass_above n B D R hn hprev
      have hInv := (inverseAt_iff_power_mass B D t k 1 (by omega) hb4 hd).mp hi
      have hBEven : 2*(B/2)=B := by omega
      have hPowMass : 2^(t+3)=2*D+B+6 := by
        have hp : 2^(t+3)=8*2^t := by
          rw [Nat.pow_add]
          omega
        omega
      have hMassLast :
          2^(t+3)+2*(R+t+1)+2*n+5=14*2^n+D+2*t := by
        omega
      have htEq : t=n+1 := by
        have hlarge : n+3<2^n := by
          have hp := hundred_mul_le_pow n hn
          omega
        by_cases htle : t≤n
        · have hpowBound : 2^(t+3)≤8*2^n := by
            have hp:= Nat.pow_le_pow_right (by decide : 0<(2:Nat))
              (show t+3≤n+3 by omega)
            have hn3 : 2^(n+3)=8*2^n := by rw [Nat.pow_add]; omega
            omega
          omega
        · have hlt : t≤n+1 := by
            by_cases hle : t≤n+1
            · exact hle
            · have htp : n+2≤t := by omega
              have hpowLarge : 32*2^n≤2^(t+3) := by
                have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat))
                  (show n+5≤t+3 by omega)
                have hn5 : 2^(n+5)=32*2^n := by rw [Nat.pow_add]; omega
                omega
              omega
          omega
      have hPowN : 2^(t+3)=16*2^n := by
        rw [htEq, show n+1+3=n+4 by omega, Nat.pow_add]
        omega
      have hPreWall : B+4*R+4*n+20=12*2^n := by omega
      omega

#print axioms BB6.Agent50DeepCone.deep_cone_to_counted
#print axioms BB6.Agent50DeepCone.deep_cone_mass_above
#print axioms BB6.Agent50DeepCone.deep_cone_right_five_exceeds_mid_cost

end BB6.Agent50DeepCone
