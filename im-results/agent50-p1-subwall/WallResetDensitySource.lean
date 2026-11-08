import WallDensityCore
import RightFiveEnergyStep
import CountedEnergyCostSource

set_option maxHeartbeats 4000000

namespace BB6.Agent50Density

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent50Energy
open BB6.Agent43CountedEnergy BB6.Agent43LastResetStrength

/-- For an original P1 counted inverse history with at most Z positive-depth
resets and total cost at most M, a dyadic buffer excludes the exact shifted
wall whenever 32*(M+n+6)*8^Z ≤ 2^n. This is a whole-word source theorem. -/
theorem source_wall_buffer
    (n M Z b d m z : Nat) (hn : 14≤n)
    (hPow : 32*(M+n+6)*8^Z ≤ 2^n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    m≤M → z≤Z →
    (12*2^n < b+4*m+4*n+20 ∨
      (b+4*m+4*n+20)+32*(M+n+6)*8^(Z-z) ≤
        12*2^n+16*(M+n+6)) := by
  induction h with
  | root =>
    intro hm hz
    left
    have h100 := BB6.Agent50RightFiveTwo.hundred_mul_le_pow n hn
    omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
    intro hmNow hzNow
    have hmPrev : m≤M := by omega
    have hzPrev : z≤Z := by
      by_cases ht : t=0
      · simpa [ht] using hzNow
      · have hnext : z+1≤Z := by simpa [ht] using hzNow
        omega
    have hprev := ih hmPrev hzPrev
    have hOdd : OddCone (14*2^n-2*n-16) 3 b d m :=
      counted_to_odd_cone _ _ _ _ _ _ hp
    have hmassSource := odd_cone_mass (14*2^n-2*n-16) 3 b d m hOdd
    have hmass : b+d+2*m+2*n+13=14*2^n := by omega
    have hInv := (inverseAt_iff_power_mass b d t k c (by omega) hb4 hd).mp hi
    have hinvMass : 2*k+c+2*t+2=b+d := by omega
    by_cases hshallow : t≤1
    · right
      have hOne : 1≤8^Z := Nat.one_le_pow Z 8 (by decide)
      have hsmallMul : 32*(M+n+6)≤32*(M+n+6)*8^Z := by
        simpa using (Nat.mul_le_mul_left (32*(M+n+6)) hOne)
      have hsmall : 32*(M+n+6)≤2^n := Nat.le_trans hsmallMul hPow
      obtain ⟨hbefore,hafter⟩ :=
        energy_step_exact n b d m t k c hmass hb4 hInv.1 hinvMass hk
      have hGap := shallow_mass_gap n (2^n) M b d m t k c
        hmNow hsmall hmass hbefore hafter hshallow
      have hidx : Z-(z+(if t=0 then 0 else 1))≤Z := by omega
      have hmono : 8^(Z-(z+(if t=0 then 0 else 1)))≤8^Z :=
        Nat.pow_le_pow_right (by decide) hidx
      have hscaled : 32*(M+n+6)*8^(Z-(z+(if t=0 then 0 else 1))) ≤
          32*(M+n+6)*8^Z :=
        Nat.mul_le_mul_left (32*(M+n+6)) hmono
      omega
    · by_cases ht2 : t=2
      · subst t
        have hnextZ : z+1≤Z := by simpa using hzNow
        have hrem : Z-z=(Z-(z+1))+1 := by omega
        have hrec := two_step_cocycle n b d m k c hmass hb4
          hInv.1 hinvMass
        rcases hprev with hhigh | hlow
        · left
          omega
        · right
          have hbudget : m+n+6≤M+n+6 := by omega
          have hlow' :
              (b+4*m+4*n+20)+
                32*(M+n+6)*8^((Z-(z+1))+1)≤
                12*2^n+16*(M+n+6) := by
            rw [← hrem]
            exact hlow
          have hnext := two_buffer_step (2^n) (M+n+6)
            (b+4*m+4*n+20)
            ((2*k-4)+4*(m+2+1)+4*n+20)
            (m+n+6) (Z-(z+1)) hbudget hlow' hrec
          simpa using hnext
      · have htdeep : 3≤t := by omega
        have hhigh := deep_high_step_above n b d m t k c hn
          hmass hb4 hInv.1 hinvMass htdeep hk
        exact Or.inl hhigh

/-- Quantitative all-cost necessary condition for an exact shifted-wall hit:
the reset count z must pay an exponential factor 8^z. -/
theorem source_wall_reset_growth
    (n b d m z : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hwall : b+4*m+4*n+20=12*2^n) :
    2^n < 32*(2*n+7+(2*n+3)*z)*8^z := by
  by_cases hnot : 2^n < 32*(2*n+7+(2*n+3)*z)*8^z
  · exact hnot
  · exfalso
    have hPow : 32*((n+1+(2*n+3)*z)+n+6)*8^z≤2^n := by
      have hCoefEq : (n+1+(2*n+3)*z)+n+6=2*n+7+(2*n+3)*z := by omega
      simpa only [hCoefEq] using (Nat.le_of_not_gt hnot)
    have hcost := source_counted_cost_linear_in_resets n b d m z hn h
    have hbar := source_wall_buffer n (n+1+(2*n+3)*z) z b d m z
      hn hPow h hcost (Nat.le_refl z)
    rcases hbar with hhigh | hlow
    · omega
    · have hlow' :
          (b+4*m+4*n+20)+32*((n+1+(2*n+3)*z)+n+6)*8^0 ≤
            12*2^n+16*((n+1+(2*n+3)*z)+n+6) := by
        simpa using hlow
      exact buffer_excludes_wall (2^n)
        ((n+1+(2*n+3)*z)+n+6) 0
        (b+4*m+4*n+20) (by omega) hlow' hwall
  
#print axioms BB6.Agent50Density.source_wall_buffer
#print axioms BB6.Agent50Density.source_wall_reset_growth
end BB6.Agent50Density
