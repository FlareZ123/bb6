import ExpandedDyadic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- The terminal exceptional source rectangle is reached under
    inverse-forcing at every exponent r>=8. The phase of the initial
    residue changes by four modulo 32 with each depth increment. The
    weaker mod-four invariant certifies every exact affine ancestor,
    including all odd depths. -/
theorem expanded_dyadic_all_depth (r x b0 t : Nat)
    (hr8 : 8≤r)
    (htmin : 7≤t) (htodd : t%4=3)
    (hpair : (x+30*t)%32=(21+4*r)%32)
    (hpow : b0+2=2^r*t) :
    ¬ BB6.Agent3.CReach x b0 := by
  have hp32 : 32 ∣ 2^r := by
    change 2^5 ∣ 2^r
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hp32
  have hdiv32 : 32 ∣ b0+2 := by
    refine ⟨u*t,?_⟩
    rw [hpow,hu]
    ac_rfl
  have hb032 : b0%32=30 := by
    have hm : (b0+2)%32=0 := Nat.mod_eq_zero_of_dvd hdiv32
    omega
  have hbase4 : (x+2*b0)%4=3 := by omega
  intro hre
  have hm0 : x+2*b0+4*(r-r)=x+2*b0 := by omega
  obtain ⟨A,hreach,hMass⟩ :=
    dyadic_back_iter r t x b0 hr8 (by omega) htmin hbase4 r x b0
      (by omega) (by omega) hpow hm0 hre
  have hV : (A+(2*t-2)+1)%32=24 := by omega
  have hY8 : (2*t-2)%8=4 := by omega
  have hA8 : A%8=3 := by omega
  have hYmin : 12≤2*t-2 := by omega
  exact exceptional_no_blank_all A (2*t-2) hA8 hY8 hV hYmin hreach

#print axioms expanded_dyadic_all_depth
end BB6.Agent46
