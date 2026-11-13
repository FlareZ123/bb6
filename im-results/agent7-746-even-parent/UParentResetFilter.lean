import UParentOddSelector
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CascadeUParentBand887
open CascadeQDepthHensel CascadeRayDepthHensel CascadeUParentBandEnvelope CascadeResetInverse

/-- On the n=887 first-tier spine, no odd U-parent can have 3-adic
    exponent five or greater: the depth selector's eighth-power residue is
    3402 mod 4374, beyond the entire first-tier depth interval. -/
theorem resetParent_U_odd_exact_n887
    (j p U z q : Nat)
    (hjlo : 6≤j) (hjhi : j≤870) (hj6 : j%6=0)
    (hp : p=2^885)
    (hform : U+2*887+2^(j+4)*1777=112*p+15)
    (hU : U=9*(2*z+5))
    (hzband : 6*p-1≤z ∧ z≤8*p-3)
    (hparent : ResetParent q z) :
    (∃ k, (6*2^k-1≤z ∧ z≤8*2^k-3) ∧ 2*z=8*2^k+q+k) ∨
    (∃ k t d, d%2=1 ∧
      (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
      2*z+5=3^(t+1)*d ∧ 2*(2^t*d)=8*2^k+q+k+5 ∧
      ((t=2 ∧ k=883 ∧ j%162=0) ∨ (t=4 ∧ k=882 ∧ j%1458=486))) := by
  have hf := resetParent_U_odd_band_filter 887 j p U z q (by omega)
    hp hform hU hzband hparent
  rcases hf with heven | ⟨k,t,d,hdodd,hband,hout,hq,hnot,hscale2,hscale4,hscale7,hscale9⟩
  · exact Or.inl heven
  · have hfac : U=3^(t+3)*d := by
      calc
        U=9*(2*z+5) := hU
        _=9*(3^(t+1)*d) := by rw [hout]
        _=3^(t+3)*d := by
          have hp3 : 3^(t+3)=9*3^(t+1) := by
            rw [show t+3=(t+1)+2 by omega,Nat.pow_add]
            rw [show (3:Nat)^2=9 by decide]
            ac_rfl
          rw [hp3]
          ac_rfl
    have hlt5 : t<5 := by
      by_cases hlt : t<5
      · exact hlt
      · have ht : 5≤t := by omega
        have hdivNat : 3^8∣U := by
          refine ⟨3^(t-5)*d,?_⟩
          rw [hfac,show t+3=8+(t-5) by omega,Nat.pow_add]
          ac_rfl
        have hdivInt : (3:Int)^8∣qNumerator 887 j := by
          rw [qNumerator_eq_U j p U hp hform]
          exact_mod_cast hdivNat
        have hsel := (qDepthResidue_iff 887 7 j (by omega)).mp hdivInt
        rcases qDepthResidue_887_table with ⟨_,_,_,_,_,_,_,h7⟩
        rw [h7] at hsel
        have hperiod : depthPeriod 7=4374 := by decide
        rw [hperiod] at hsel
        have hmod : j%4374=j := Nat.mod_eq_of_lt (by omega)
        rw [hmod] at hsel
        omega
    have hcases : t=2 ∨ t=4 := by omega
    rcases hcases with ht2 | ht4
    · have hdivNat : 3^5∣U := by
        refine ⟨d,?_⟩
        rw [hfac,ht2]
      have hdivInt : (3:Int)^5∣qNumerator 887 j := by
        rw [qNumerator_eq_U j p U hp hform]
        exact_mod_cast hdivNat
      have hsel := (qDepthResidue_iff 887 4 j (by omega)).mp hdivInt
      rcases qDepthResidue_887_table with ⟨_,_,_,_,h4,_,_,_⟩
      rw [h4] at hsel
      have hperiod : depthPeriod 4=162 := by decide
      rw [hperiod] at hsel
      have hk : k=883 := by have hs:=hscale2 ht2; omega
      exact Or.inr ⟨k,t,d,hdodd,hband,hout,hq,Or.inl ⟨ht2,hk,hsel⟩⟩
    · have hdivNat : 3^7∣U := by
        refine ⟨d,?_⟩
        rw [hfac,ht4]
      have hdivInt : (3:Int)^7∣qNumerator 887 j := by
        rw [qNumerator_eq_U j p U hp hform]
        exact_mod_cast hdivNat
      have hsel := (qDepthResidue_iff 887 6 j (by omega)).mp hdivInt
      rcases qDepthResidue_887_table with ⟨_,_,_,_,_,_,h6,_⟩
      rw [h6] at hsel
      have hperiod : depthPeriod 6=1458 := by decide
      rw [hperiod] at hsel
      have hk : k=882 := by have hs:=hscale4 ht4; omega
      exact Or.inr ⟨k,t,d,hdodd,hband,hout,hq,Or.inr ⟨ht4,hk,hsel⟩⟩


end CascadeUParentBand887
