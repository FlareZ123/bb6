import AffineParityDepth
import EvenTargetOrbit
import M8M16Composition
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- General 2-adic barrier for the exact forced-affine predecessor
    normalizer, connected to a source-certified mod-eight quotient. -/
theorem normalize_even_depth_m8_forbidden (a k : Nat)
    (ha : a%4=3) (hmass : (a+2*k)%8=7)
    (hdepth : oddDepth k%2=0)
    (hfact : ∃ q:Nat, k+2=2^(oddDepth k)*(8*q+6)) :
    ¬ CReach a k := by
  let p := affineNormalize a k
  obtain ⟨hm,hs,_⟩ := normalize_three_depth_invariants a k ha
  change p.1+2*p.2+4*oddDepth k=a+2*k at hm
  change 2^(oddDepth k)*(p.2+2)=k+2 at hs
  obtain ⟨q,hq⟩ := hfact
  have hp2sum : p.2+2=8*q+6 := by
    apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0<2))
    exact hs.trans hq
  have hp2 : p.2%8=4 := by omega
  have hp1 : p.1%8=7 := by omega
  intro hr
  have hrnorm := (reach_iff_normalize a k).mp hr
  have hpa : p.1=8*(p.1/8)+7 := by omega
  have hpk : p.2=8*(p.2/8)+4 := by omega
  change CReach p.1 p.2 at hrnorm
  rw [hpa,hpk] at hrnorm
  exact blank_no_m8_cylinder _ _ hrnorm

/-- Explicit depth certificate on a whole modulo-32 parameter class. -/
theorem depth_case_21 (u : Nat) (hu : u%32=21) :
    oddDepth (21*u-3)=2 := by
  let K : Nat := 21*u-3
  have h0 : 4≤K ∧ K%4=2 := by dsimp [K]; omega
  have h1 : 4≤(K-2)/2 ∧ ((K-2)/2)%4=2 := by dsimp [K]; omega
  have h2 : ¬ (4≤(((K-2)/2-2)/2) ∧ (((K-2)/2-2)/2)%4=2) := by
    dsimp [K]; omega
  change oddDepth K=2
  rw [oddDepth,dif_pos h0,oddDepth,dif_pos h1,oddDepth,dif_neg h2]

/-- Exact all-time exclusion for the universal high inverse parent
    when its residual parameter is twenty-one modulo thirty-two. -/
theorem high_parent_twentyone_unreachable (u : Nat) (hu : u%32=21) :
    ¬ CReach (22*u-3) (21*u-3) := by
  have ha : (22*u-3)%4=3 := by omega
  have hmass : ((22*u-3)+2*(21*u-3))%8=7 := by omega
  have hd : oddDepth (21*u-3)%2=0 := by
    rw [depth_case_21 u hu]
  have hq : ∃ q:Nat, (21*u-3)+2=2^(oddDepth (21*u-3))*(8*q+6) := by
    refine ⟨(21*u-25)/32,?_⟩
    rw [depth_case_21 u hu]
    change 21*u-3+2=4*(8*((21*u-25)/32)+6)
    omega
  exact normalize_even_depth_m8_forbidden (22*u-3) (21*u-3)
    ha hmass hd hq

/-- Another completely disjoint infinite low-gate residue class,
    requiring two extra forced affine inversions after the high source. -/
theorem low_gate_fortytwo_mod64_unreachable (t : Nat)
    (ht : 1≤t) (hmod : t%64=42) :
    ¬ BB6.Agent3.CReach 1 (16*t+4) := by
  intro h
  obtain ⟨r,u,hu,hindex,hparent⟩ :=
    (BB6.Agent3.low_gate_all_parents_iff t ht).mp h
  have hr0 : r=0 := by
    cases r with
    | zero => rfl
    | succ n =>
      have hfac : t=8*(4^n*u) := by
        calc
          t = 2*(4^(n+1)*u) := hindex
          _ = 2*((4^n*4)*u) := by rw [Nat.pow_succ]
          _ = (2*4)*(4^n*u) := by ac_rfl
          _ = 8*(4^n*u) := by rfl
      rw [hfac] at hmod
      omega
  subst r
  have hindex2 : t=2*u := by simpa using hindex
  have hu32 : u%32=21 := by omega
  have hsub : 32*u-(11*u+3)=21*u-3 := by omega
  have hsource : BB6.Agent15.CReach (22*u-3) (21*u-3) := by
    simpa [hsub] using hparent
  exact high_parent_twentyone_unreachable u hu32 hsource

/-- New infinite exclusion in Machine C's first halting family, parameter
    m = 456 modulo 1024. This has survived the previously published
    congruence filter, but is blocked by a longer exact inverse chain. -/
theorem first_halt_m456_mod1024_unreachable (m k : Nat)
    (hm : m%1024=456)
    (hk : k+3*m+4=2^(2*m+3)) : ¬ BB6.Agent3.CReach 1 k := by
  have hmpos : 4≤m := by omega
  have hpow : 1024 ∣ 2^(2*m+3) := by
    have hh : 2^10 ∣ 2^(2*m+3) := Nat.pow_dvd_pow 2 (by omega)
    simpa using hh
  have hmod : (k+3*m+4)%1024=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hk1024 : k%1024=676 := by omega
  let t : Nat := (k-4)/16
  have ht : k=16*t+4 := by dsimp [t]; omega
  have htpos : 1≤t := by dsimp [t]; omega
  have htm : t%64=42 := by dsimp [t]; omega
  intro hr
  rw [ht] at hr
  exact low_gate_fortytwo_mod64_unreachable t htpos htm hr

#print axioms normalize_even_depth_m8_forbidden
#print axioms high_parent_twentyone_unreachable
#print axioms low_gate_fortytwo_mod64_unreachable
#print axioms first_halt_m456_mod1024_unreachable
end BB6.Agent11
