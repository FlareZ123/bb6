import One307Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13U17
open BB6.Agent46

/-- Entire original-source forbidden affine ray: no blank section return
    to (180*u+28,166*u+25) with u=17 modulo32. Both exact incoming
    parents have odd right counter and sum two modulo four. -/
theorem source_rectangle_u17_mod32 (u : Nat) (hu : u%32=17) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/32
  have hU : u=32*t+17 := by
    have h := Nat.mod_add_div u 32
    dsimp [t]
    omega
  have hL0 :
      BB6.Agent13TwoParent.parentLeft (180*u+28) (166*u+25) 0 =
      5536*t+2965 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR0 :
      BB6.Agent13TwoParent.parentRight (180*u+28) (166*u+25) 0 =
      5424*t+2905 := by
    simp [BB6.Agent13TwoParent.parentRight,
      BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hL2 :
      BB6.Agent13TwoParent.parentLeft (180*u+28) (166*u+25) 2 =
      1384*t+739 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR2 :
      BB6.Agent13TwoParent.parentRight (180*u+28) (166*u+25) 2 =
      7500*t+4015 := by
    simp [BB6.Agent13TwoParent.parentRight,
      BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have h0 : BB6.Agent11SixForced.sixForcedExcluded
      (BB6.Agent13TwoParent.parentLeft (180*u+28) (166*u+25) 0)
      (BB6.Agent13TwoParent.parentRight (180*u+28) (166*u+25) 0)=true := by
    rw [hL0,hR0]
    exact BB6.Agent13SourceRect.six_excludes_odd_sum_two
      _ _ (by omega) (by omega) (by omega)
  have h2 : BB6.Agent11SixForced.sixForcedExcluded
      (BB6.Agent13TwoParent.parentLeft (180*u+28) (166*u+25) 2)
      (BB6.Agent13TwoParent.parentRight (180*u+28) (166*u+25) 2)=true := by
    rw [hL2,hR2]
    exact BB6.Agent13SourceRect.six_excludes_odd_sum_two
      _ _ (by omega) (by omega) (by omega)
  exact BB6.Agent13TwoParent.two_parent_normalizer_excluded
    (180*u+28) (166*u+25)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) h0 h2

/-- Four exact source inverse edges connect the low target to the affine
    forbidden ray for every u. -/
theorem no_one_256u51_u17_mod32 (u : Nat) (hu : u%32=17) :
    ¬ BB6.Agent3.CReach 1 (256*u+51) := by
  intro hr
  exact (source_rectangle_u17_mod32 u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

/-- Original-source full-time exclusion for low stopping indices
    m=512*z+67 with z=13 mod16. This is eight of 128 residue classes
    within that m=67 mod512 progression, not a finite experiment. -/
theorem low_stop_m67_z13_mod16_unreachable
    (z m k : Nat)
    (hm : m=512*z+67)
    (hz : z%16=13)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 8192 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^13 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^13=8192 by decide] using h
  have hpmod : (2^(2*m+3))%8192=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%8192=4403 := by
    have hs : (k+3*m+4)%8192=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 32*(k/8192)+17
  have hu : u%32=17 := by
    dsimp [u]
    omega
  have hk : k=256*u+51 := by
    have hdecomp := Nat.mod_add_div k 8192
    rw [hkmod] at hdecomp
    dsimp [u]
    omega
  rw [hk]
  exact no_one_256u51_u17_mod32 u hu

#print axioms low_stop_m67_z13_mod16_unreachable
end BB6.Agent13U17
