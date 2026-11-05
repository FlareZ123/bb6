import S5FirstInverse
import UniformOrbitIff
import Agent3CImage
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

theorem reach_forced_parent (x y u v : Nat) (hx : 5<x)
    (hp : ∀ a k, secNext (a,k)=some (x,y) → a=u ∧ k=v)
    (hr : BB6.Agent3.CReach x y) : BB6.Agent3.CReach u v := by
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases hc : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hc] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hed : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hc] using ht
          obtain ⟨ha,hk⟩ := hp a k hed
          refine ⟨n,?_⟩
          simpa only [ha,hk] using hc

theorem s5_three_link_forces_bad (q : Nat) :
    BB6.Agent3.CReach (17792*q+1379) (7488*q+581) →
    BB6.Agent3.CReach (27736*q+2140) (2516*q+193) := by
  intro hr
  have hp : BB6.Agent3.CReach (12640*q+978) (10064*q+778) := by
    apply reach_forced_parent (17792*q+1379) (7488*q+581)
      (12640*q+978) (10064*q+778) (by omega) ?_ hr
    intro a k hed
    exact s5_first_inverse q a k hed
  have hb : BB6.Agent3.CReach (22704*q+1754) (5032*q+388) := by
    apply reach_forced_parent (12640*q+978) (10064*q+778)
      (22704*q+1754) (5032*q+388) (by omega) ?_ hp
    intro a k hed
    obtain ⟨ha,hk⟩ := section_eveneven_sum_four_mod8_inverse
      a k (12640*q+978) (10064*q+778)
      (by omega) (by omega) (by omega) (by omega) hed
    constructor <;> omega
  apply reach_forced_parent (22704*q+1754) (5032*q+388)
      (27736*q+2140) (2516*q+193) (by omega) ?_ hb
  intro a k hed
  obtain ⟨ha,hk⟩ := section_even_sum_two_mod4_inverse
    a k (22704*q+1754) (5032*q+388)
    (by omega) (by omega) (by omega) hed
  constructor <;> omega

theorem s5_bad_ancestor_unreachable (q : Nat) :
    ¬ BB6.Agent3.CReach (27736*q+2140) (2516*q+193) := by
  rintro ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
  | succ n =>
      have hs := BB6.Agent3.blank_section_odd_image n
        (27736*q+2140) (2516*q+193) ht
        (by omega) (by omega)
      omega

theorem blank_no_s5_affine (q : Nat) :
    ¬ BB6.Agent3.CReach (17792*q+1379) (7488*q+581) := by
  intro h
  exact s5_bad_ancestor_unreachable q (s5_three_link_forces_bad q h)

theorem blank_no_s5_one_gate (q : Nat) :
    ¬ BB6.Agent3.CReach 1 (16384*q+1284) := by
  intro hr
  have hs : 1≤64*q+5 := by omega
  have hodd : (64*q+5)%2=1 := by omega
  have harg : 256*(64*q+5)+4=16384*q+1284 := by omega
  have hp := (uniform_one_gate_reach_iff_affine (64*q+5) hs hodd).mp
      (by simpa only [harg] using hr)
  have hfirst : 278*(64*q+5)-11=17792*q+1379 := by omega
  have hsecond : 117*(64*q+5)-4=7488*q+581 := by omega
  rw [hfirst,hsecond] at hp
  exact blank_no_s5_affine q hp

theorem blank_no_low_halt_depth5032 (m k : Nat)
    (hm : m%16384=5032)
    (heq : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hlarge : 6≤m := by omega
  have hpow : 16384 ∣ 2^(2*m+3) := by
    change 2^14 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hpow
  have hmod : k%16384=1284 := by omega
  have hk : k=16384*(k/16384)+1284 := by omega
  intro hr
  rw [hk] at hr
  exact blank_no_s5_one_gate (k/16384) hr

#print axioms s5_three_link_forces_bad
#print axioms s5_bad_ancestor_unreachable
#print axioms blank_no_s5_affine
#print axioms blank_no_s5_one_gate
#print axioms blank_no_low_halt_depth5032

end BB6.Agent46
