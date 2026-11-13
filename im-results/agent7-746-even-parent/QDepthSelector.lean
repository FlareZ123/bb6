import QDepthSelectorBase
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CascadeQDepthHensel
open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

theorem qDepthResidue_iff (n k j : Nat)
    (hn:n%6=4 ∨ n%6=5) :
    ((3:Int)^(k+1)∣qNumerator n j) ↔
      j%depthPeriod k=qDepthResidue n k := by
  induction k generalizing j with
  | zero =>
      have h:=q_mod_three_even_iff n j hn
      change (3:Int)∣qNumerator n j ↔ j%2=0
      rw [Int.dvd_iff_emod_eq_zero]
      simpa using h
  | succ k ih =>
      let p:=depthPeriod k
      let pn:=depthPeriod (k+1)
      let b:=qDepthResidue n k
      let d:=henselDigit
        (qNumerator n b/(3:Int)^(k+1))
        (8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)
      have hstep:pn=3*p:=depthPeriod_next k
      have hdiv:(3:Int)^(k+1)∣(3:Int)^(k+2):=by
        refine ⟨3,?_⟩
        rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
      constructor
      · intro hx
        have hz:(3:Int)^(k+2)∣qNumerator n (j%pn):=
          (q_period_mod_dvd_iff n j (k+1)).mp hx
        have hlo:(3:Int)^(k+1)∣qNumerator n (j%pn):=by
          cases hz with
          | intro w hw =>
            cases hdiv with
            | intro v hv =>
              refine ⟨v*w,?_⟩
              rw [hw,hv]
              ac_rfl
        have hb:(j%pn)%p=b:=(ih (j%pn)).mp hlo
        have hp:0<p:=depthPeriod_pos k
        have hjlt:j%pn<3*p:=by
          have h:=Nat.mod_lt j (depthPeriod_pos (k+1))
          simpa only [pn,hstep] using h
        have ht:(j%pn)/p<3:=(Nat.div_lt_iff_lt_mul hp).mpr hjlt
        have heq:j%pn=b+((j%pn)/p)*p:=by
          have hh:=Nat.mod_add_div' (j%pn) p
          omega
        have hd':=((q_small_digit_unique n k hn ((j%pn)/p) ht).mp
          (by rw [ₐheq]; exact hz))
        have hnext:qDepthResidue n (k+1)=b+d*p:=rfl
        have hdnum:(j%pn)/p=d:=by simpa only [b,d] using hd'
        have htarget:j%pn=b+d*p:=by rw [←hdnum]; exact heq
        change j%pn=qDepthResidue n (k+1)
        rw [hnext]
        exact htarget
      · intro hx
        apply (q_period_mod_dvd_iff n j (k+1)).mpr
        rw [hx]
        exact qDepthResidue_good n (k+1) hn

/-- Exactly one residue is selected in each full depth period. -/
theorem qDepthResidue_unique_in_period (n k j : Nat)
    (hn:n%6=4 ∨ n%6=5) (hj:j<depthPeriod k) :
    ((3:Int)^(k+1)∣qNumerator n j) ↔ j=qDepthResidue n k := by
  rw [qDepthResidue_iff n k j hn]
  simp only [Nat.mod_eq_of_lt hj]


end CascadeQDepthHensel
