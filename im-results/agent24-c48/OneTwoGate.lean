import EvenRightSixOrbit
import ReachAffine
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Entire one-left-counter residue 2 mod16, excluding only the small
    exceptional counter 2, has a two-step forced inverse into the
    globally forbidden (3 mod4,3 mod4) section quadrant. -/
theorem blank_no_one_two_mod16 (t : Nat) (ht : 1≤t) :
    ¬ BB6.Agent3.CReach 1 (16*t+2) := by
  intro hr
  have hfirst : BB6.Agent3.CReach (16*t+1) (8*t) := by
    have hh := (six_even_right_blank_reach_iff
      1 (16*t+2) (by omega) (by omega) (by omega) (by omega)).mp hr
    have hx : 1+(16*t+2)-2=16*t+1 := by omega
    have hy : ((16*t+2)-2)/2=8*t := by omega
    rw [hx,hy] at hh
    exact hh
  have hsecond : BB6.Agent3.CReach (24*t-1) (4*t-1) := by
    have hh := (BB6.Agent15.blank_reach_iff_affine
      (16*t+1) (8*t) (by omega) (by omega) (by omega)).mp hfirst
    have hx : (16*t+1)+(8*t)-2=24*t-1 := by omega
    have hy : ((8*t)-2)/2=4*t-1 := by omega
    rw [hx,hy] at hh
    exact hh
  rcases hsecond with ⟨n,hn⟩
  have ha : 24*t-1=4*(6*t-1)+3 := by omega
  have hk : 4*t-1=4*(t-1)+3 := by omega
  rw [ha,hk] at hn
  exact BB6Agent38.blank_section_no_33 n (6*t-1) (t-1) hn

private theorem pow_two_linear (m : Nat) :
    4*m+8 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2^(2*(m+1)+3)=4*(2^(2*m+3)) := by
        calc
          2^(2*(m+1)+3)=2^((2*m+3)+2) := by congr 1 <;> omega
          _=2^(2*m+3)*2^2 := by rw [Nat.pow_add]
          _=2^(2*m+3)*4 := by rfl
          _=4*(2^(2*m+3)) := by ac_rfl
      rw [he]
      omega

/-- Source-exact low stopping family exclusion for every stopping depth
    m=14 modulo16, a complete congruence class of positive density. -/
theorem blank_no_low_halt_depth14 (m k : Nat)
    (hm : m%16=14)
    (heq : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hm14 : 14≤m := by omega
  have hpow_lower := pow_two_linear m
  have hk18 : 18≤k := by omega
  have hdiv : 16 ∣ 2^(2*m+3) := by
    change 2^4 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hdiv
  have hmod : k%16=2 := by omega
  have hk : k=16*(k/16)+2 := by omega
  have ht : 1≤k/16 := by omega
  intro hr
  rw [hk] at hr
  exact blank_no_one_two_mod16 (k/16) ht hr

#print axioms blank_no_one_two_mod16
#print axioms blank_no_low_halt_depth14
end BB6.Agent46
