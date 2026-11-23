import CThreeSixAllCriterion
import M32SectionEmbedding
import HighSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13M32Integration

/-- A source-certified finite M32 condition added to the strongest current
    high parameter gate. The implication preserves the small j<3 or m<2
    cases, which are outside Agent 4's generic M32 stopping-family bridge. -/
def highAllowedM32 (j m : Nat) : Prop :=
  BB6.Agent11SixCriterion.highAllowed j m ∧
    ((3≤j ∧ 2≤m) → ¬ CCert.highPairGood (j%32) (m%32))

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- Exact original-blank Machine C halting criterion with the complete
    M32 high-pair quotient condition integrated into the current
    C58 + all-depth + diagonal + six-sector criterion. The low branch
    remains unchanged because its M32 m%32=24 family is already covered
    by the existing low source sieve. -/
theorem blank_halts_iff_six_m32 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedM32 j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11SixAll.blank_halts_iff_six_both]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mp hroot
      have hnot : (3≤j ∧ 2≤m) →
          ¬ CCert.highPairGood (j%32) (m%32) := by
        intro hbounds hgood
        rcases hbounds with ⟨hj,hm⟩
        have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (high_bound j m)
          omega
        have hr15 : BB6.Agent15.CReach (2*j+3) k := by
          simpa [BB6.Agent3.CReach, BB6.Agent15.CReach] using hr
        have hline : BB6CLine.Reach (2*j+3,k,0) :=
          BB6.Agent15.m32_section_reach_embeds hr15
        exact (BB6.Agent4M32.high32_forbidden_source
          j m k hj hm hstop hgood) hline
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- The M32 quotient certifies the residue pair (0,13) as absent. -/
theorem m32_pair_0_13_good :
    CCert.highPairGood 0 13 := by
  decide

/-- The same (0,13) family is invisible to the six-forced inverse
    normalizer: its first state already has residues (x,k,x+k)=(3,4,7)
    modulo 8, and none of the six source gates can fire. -/
theorem sixForced_not_excluded_0_13
    (j m k : Nat) (hm : 2≤m)
    (hjr : j%32=0) (hmr : m%32=13)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent11SixForced.sixForcedExcluded (2*j+3) k = false := by
  have hpow : 8 ∣ 2^(2*m+2) := by
    have hp : 2^3 ∣ 2^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    norm_num at hp
    exact hp
  have hprod : 8 ∣ 2^(2*m+2)*(j+3) :=
    dvd_mul_of_dvd_left hpow (j+3)
  have hP : (2^(2*m+2)*(j+3))%8=0 :=
    Nat.mod_eq_zero_of_dvd hprod
  have hB : (j+3*m+5)%8=4 := by
    have hj8 : j%8=0 := by omega
    have hm8 : m%8=5 := by omega
    omega
  have hk8 : k%8=4 := by omega
  have hx8 : (2*j+3)%8=3 := by
    have hj4 : j%4=0 := by omega
    omega
  have hx16 : (2*j+3)%16 ≠ 5 := by
    have hj8 : j%8=0 ∨ j%8=4 := by omega
    rcases hj8 with h | h <;> omega
  have hsum8 : ((2*j+3)+k)%8=7 := by omega
  have hsum4 : ((2*j+3)+k)%4=3 := by omega
  have hkeven : k%2=0 := by omega
  simp [BB6.Agent11SixForced.sixForcedExcluded,
    BB6.Agent11SixForced.sixForcedNormalize,
    BB6.Agent3.oddLowGate,
    BB6.Agent3.evenSevenGate,
    BB6.Agent3.evenAffineGate,
    BB6.Agent46.sixEvenRightGate,
    BB6.Agent3ValSix.valSixGate,
    BB6.Agent11SixForced.evenOddFourGate,
    hx8,hx16,hsum8,hsum4,hkeven]

/-- Infinite source-level exclusion for the high stopping family
    j=0 (mod 32), m=13 (mod 32), j>=3, m>=2. -/
theorem m32_0_13_family_no_root
    (j m k : Nat) (hj : 3≤j) (hm : 2≤m)
    (hjr : j%32=0) (hmr : m%32=13)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  intro hr
  have hr15 : BB6.Agent15.CReach (2*j+3) k := by
    simpa [BB6.Agent3.CReach, BB6.Agent15.CReach] using hr
  have hline : BB6CLine.Reach (2*j+3,k,0) :=
    BB6.Agent15.m32_section_reach_embeds hr15
  have hgood : CCert.highPairGood (j%32) (m%32) := by
    simpa [hjr,hmr] using m32_pair_0_13_good
  exact (BB6.Agent4M32.high32_forbidden_source
    j m k hj hm hstop hgood) hline

#print axioms blank_halts_iff_six_m32
#print axioms m32_pair_0_13_good
#print axioms m32_0_13_family_no_root

end BB6.Agent13M32Integration
