import U5Q0SourceOnlyW1021
import U5SourceOnlyHighStop
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-!
End-to-end source-only exclusion on the new residual cylinder
w=1021 (mod 1024). The arithmetic lift identifies the q-fan parameter
z=2 (mod 128); the two exact source-parent branches are discharged in
U5Q0SourceOnlyW1021.lean. The existing U5 M8 terminal and m=0 feeder
bridges then lift this to the authentic high stopping root.

This is a Lean draft pending local Lean 4.36.0-rc2 compilation and
an exported axiom audit. No finite quotient is used in this dependency
chain, and this result does not decide the full U5 family or BB(6).
-/

namespace BB6.Agent4U5SourceOnlyHighStopW1021
open BB6.Agent3
open BB6.Agent3U5DepthFan

private theorem succ_le_two_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : 2^(n+1)=2^n*2 := by rw [Nat.pow_succ]
      omega

private theorem pow_two_mod_three (n : Nat) :
    2^n%3 = if n%2=0 then 1 else 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.pow_succ,Nat.mul_mod]
      rw [ih]
      by_cases h : n%2=0
      · have hn : (n+1)%2=1 := by omega
        simp [h,hn]
      · have hn : (n+1)%2=0 := by omega
        simp [h,hn]

/-- The exact residual identity and the cylinder w=1021 (mod 1024)
force t=123+168*z with z=2 (mod 128). -/
theorem u5_w1021_t_param (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%1024=1021) :
    ∃ v, t=123+168*(128*v+2) := by
  have hId := BB6.Agent3U5M16Residual.u5_m8_t_identity
    w s m t hs hm hp
  have hrmod2 : (201+3360*w)%2=1 := by omega
  have hpow3 : (2^(201+3360*w))%3=2 := by
    rw [pow_two_mod_three]
    simp [hrmod2]
  have hpow3mul : (20*2^(201+3360*w))%3=1 := by
    rw [Nat.mul_mod,hpow3]
    norm_num
  have hpow7 : (2^(201+3360*w))%7=1 := by
    rw [show 201+3360*w=3*(67+1120*w) by omega,
      Nat.pow_mul,Nat.pow_mod]
    have hbase : (2:Nat)^3%7=1 := by decide
    rw [hbase]
    simp
  have hpow7mul : (20*2^(201+3360*w))%7=6 := by
    rw [Nat.mul_mod,hpow7]
    norm_num
  have ht3 : t%3=0 := by
    have hmod : (211*t+1360+22155*w)%3 =
        (20*2^(201+3360*w))%3 := by rw [hId]
    rw [hpow3mul] at hmod
    omega
  have ht7 : t%7=4 := by
    have hmod : (211*t+1360+22155*w)%7 =
        (20*2^(201+3360*w))%7 := by rw [hId]
    rw [hpow7mul] at hmod
    omega
  have hdiv8 : 8∣2^(201+3360*w) := by
    change 2^3∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpow8 : (2^(201+3360*w))%8=0 :=
    Nat.mod_eq_zero_of_dvd hdiv8
  have hpow8mul : (20*2^(201+3360*w))%8=0 := by
    rw [Nat.mul_mod,hpow8]
    norm_num
  have ht8 : t%8=3 := by
    have hmod : (211*t+1360+22155*w)%8 =
        (20*2^(201+3360*w))%8 := by rw [hId]
    rw [hpow8mul] at hmod
    omega
  have ht168 : t%168=123 := by omega
  have hdiv1024 : 1024∣2^(201+3360*w) := by
    change 2^10∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpow1024 : (2^(201+3360*w))%1024=0 :=
    Nat.mod_eq_zero_of_dvd hdiv1024
  have hpow1024mul : (20*2^(201+3360*w))%1024=0 := by
    rw [Nat.mul_mod,hpow1024]
    norm_num
  have hmod1024 : (211*t+1360+22155*w)%1024=0 := by
    rw [hId]
    exact hpow1024mul
  have ht1024 : t%1024=459 := by
    have hconst : (211*459+1360+22155*1021)%1024=0 := by decide
    have hinv : 211*859=1024*177+1 := by norm_num
    omega
  let z := (t-123)/168
  have htEq : t=123+168*z := by
    dsimp [z]
    omega
  have hzmod : z%128=2 := by
    rw [htEq] at ht1024
    omega
  obtain ⟨v,hv⟩ : ∃ v, z=128*v+2 := by
    refine ⟨z/128,?_⟩
    omega
  exact ⟨v,by rw [htEq,hv]⟩

/-- The y=3 terminal of the U5 M8 residual is unreachable on
w=1021 (mod 1024). Its q=0 parent is excluded by the new
z=2 (mod 128) source-only fan; q=1 is odd-right sum two; q>=2
contradicts m+1=1 (mod 8). -/
theorem blank_no_u5_residual_m8w_w1021 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%1024=1021) :
    ¬ CReach (302+512*s-4*(201+3360*w)) 3 := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  have hm' : 32*s=32+105*(8*w)+m := by omega
  have hm8 : m%8=0 := by
    have hmod : (32*s)%8=(32+840*w+m)%8 := by rw [hm]
    have hleft : (32*s)%8=0 := by simp [Nat.mul_mod]
    have hright : (32+840*w+m)%8=m%8 := by
      simp [Nat.add_mod,Nat.mul_mod]
    rw [hleft,hright] at hmod
    exact hmod.symm
  have hp8 : (m+1)%8=1 := by simp [Nat.add_mod,hm8]
  have hrpow : 201+3360*w+1≤2^(201+3360*w) := succ_le_two_pow _
  have hlin : 211*(27*w+1)+129≤5*(201+3360*w+1) := by omega
  have hbig : 211*(27*w+1)+129≤5*2^(201+3360*w) := by omega
  have hsge : 27*w+1≤s := by omega
  have hmge : 24*w≤m := by omega
  have hwge : 1021≤w := by omega
  have hpge : 3≤m+1 := by omega
  intro hreach
  obtain ⟨time,ht⟩ := hreach
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
  | succ n =>
      cases hr : BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hr] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : BB6.Agent46.secNext (a,k)=
              some (302+512*s-4*(201+3360*w),3) := by
            simpa [BB6.Agent8Section.run,hr] using ht
          have hM : 201+420*(8*w)=201+3360*w := by omega
          have hsec : BB6.Agent46.secNext (a,k)=
              some (302+512*s-4*(201+420*(8*w)),3) := by
            simpa only [hM] using hedge
          rcases u5_residual_y3_parent_fan (8*w) s m a k hs' hm' hsec with
            hq0 | ⟨q,U,hqpos,hqbound,hdecomp,ha,hk⟩
          · have hparent : CReach (8*(m+1)-3) (4*(m+1)-1) := by
              rw [hq0.1,hq0.2] at hr
              exact ⟨n,hr⟩
            let t := (m+1)/8
            have hp : m+1=8*t+1 := by dsimp [t]; omega
            have htpos : 1≤t := by dsimp [t]; omega
            obtain ⟨v,hv⟩ :=
              u5_w1021_t_param w s m t hs hm hp hw
            have hX := BB6.Agent4U5SourceOnly.q0_parent_reach_implies_X
              t htpos hparent
            have hX' : CReach
                (44*(123+168*(128*v+2))-1)
                (42*(123+168*(128*v+2))-1) := by
              simpa only [hv] using hX
            exact BB6.Agent4U5SourceOnlyW1021.q0_X_not_reach_t123_z2mod128
              v hX'
          · by_cases hq1 : q=1
            · subst q
              have hUeq : U=m+1 := by simpa using hdecomp.symm
              have haEq : a=2*(m+1)-3 := by omega
              have hkEq : k=7*(m+1)-4 := by omega
              have hparent : CReach (2*(m+1)-3) (7*(m+1)-4) := by
                rw [haEq,hkEq] at hr
                exact ⟨n,hr⟩
              have hbad := BB6.Agent11High.blank_no_odd_sum_two
                (2*(m+1)-3) (7*(m+1)-4)
                (by omega) (by omega) (by omega)
              exact hbad hparent
            · have hq2 : 2≤q := by omega
              have h4pow : 4∣2^(2*q-2) := by
                change 2^2∣2^(2*q-2)
                exact Nat.pow_dvd_pow 2 (by omega)
              rcases h4pow with ⟨r,hrpow⟩
              have h4 : 4∣m+1 := by
                refine ⟨r*U,?_⟩
                rw [hdecomp,hrpow]
                ac_rfl
              have h4mod : (m+1)%4=0 := Nat.mod_eq_zero_of_dvd h4
              omega

/-- The B_s feeder of the high m=0 stop is unreachable on this cylinder. -/
theorem blank_no_u5_B_s_m8w_w1021 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%1024=1021) :
    ¬ CReach (54+90*s) (127+211*s) := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  intro hB
  have hterminal :=
    (BB6.Agent3U5M8.u5_residual_six_even_right_chain (8*w) s hs').mp hB
  have hM : 201+420*(8*w)=201+3360*w := by omega
  have hterminal' : CReach (302+512*s-4*(201+3360*w)) 3 := by
    simpa only [hM] using hterminal
  exact blank_no_u5_residual_m8w_w1021 w s m hs hm hw hterminal'

/-- Both exact source parents of A_s are excluded, closing the full
A_s branch on w=1021 (mod 1024). -/
theorem blank_no_u5_A_s_m8w_w1021 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%1024=1021) :
    ¬ CReach (130+208*s) (94+152*s) := by
  have hdiv : 8∣2^(201+3360*w) := by
    change 2^3∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod : (2^(201+3360*w))%8=0 := Nat.mod_eq_zero_of_dvd hdiv
  have hsmod : (211*s+129)%8=0 := by
    rw [hs,Nat.mul_mod,hpowmod]
  have hs8 : s%8=5 := by omega
  have hL := BB6.Agent11M0SumZeroVerified.blank_no_L_s_mod8_five s hs8
  have hB := blank_no_u5_B_s_m8w_w1021 w s m hs hm hw
  intro hA
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (130+208*s) (94+152*s) (by omega) hA
  have hfan := BB6.Agent11M0SumZeroVerified.m0_odd_ray_parent
    s a k (by omega) hstep
  rcases hfan with hLparent | hBparent
  · have hLreach : CReach (222+360*s) (46+76*s) := by
      rw [hLparent.1,hLparent.2] at hprev
      exact hprev
    exact hL hLreach
  · have hBreach : CReach (54+90*s) (127+211*s) := by
      rw [hBparent.1,hBparent.2] at hprev
      exact hprev
    exact hB hBreach

/-- The high m=0 stopping root j=39+64*s is excluded for the
U5 residual family w=1021 (mod 1024), using only exact source
predecessors and the authentic blank-section orbit. -/
theorem blank_no_high_m0_u5_w1021 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%1024=1021) :
    ¬ CReach (2*(39+64*s)+3) (3*(39+64*s)+7) := by
  intro hroot
  let t := 2*s+1
  have hroot' : CReach (17+64*t) (28+96*t) := by
    have hx : 2*(39+64*s)+3=17+64*t := by dsimp [t]; omega
    have hy : 3*(39+64*s)+7=28+96*t := by dsimp [t]; omega
    simpa only [hx,hy] using hroot
  have hA := BB6.Agent11M0SumZeroVerified.mzero_first_two_reach t hroot'
  have hx : 26+104*t=130+208*s := by dsimp [t]; omega
  have hy : 18+76*t=94+152*s := by dsimp [t]; omega
  have hA' : CReach (130+208*s) (94+152*s) := by
    simpa only [hx,hy] using hA
  exact blank_no_u5_A_s_m8w_w1021 w s m hs hm hw hA'

/-- Every w=1024*n+1021 residual is non-vacuous and has an
authentic blank-unreachable high m=0 root. The root parameter remains
j=18791 (mod 32768), so this is an additional parameter cylinder
inside the existing containing root residue, not a new density claim. -/
theorem every_w1021_residual_has_unreachable_root (n : Nat) :
    ∃ s m,
      211*s+129=5*2^(201+3360*(1024*n+1021)) ∧
      32*s=32+840*(1024*n+1021)+m ∧
      (39+64*s)%32768=18791 ∧
      ¬ CReach (2*(39+64*s)+3) (3*(39+64*s)+7) := by
  obtain ⟨s,m,hs,hm,_,_⟩ :=
    BB6.Agent4U5SourceOnlyHighStop.u5_residual_nonempty
      (1024*n+1021)
  have hw : (1024*n+1021)%1024=1021 := by omega
  have hroot := blank_no_high_m0_u5_w1021
    (1024*n+1021) s m hs hm hw
  have hres :=
    BB6.Agent4U5SourceOnlyHighStop.u5_high_root_parameter_residue
      (1024*n+1021) s hs
  exact ⟨s,m,hs,hm,hres.1,hroot⟩

#print axioms pow_two_mod_three
#print axioms u5_w1021_t_param
#print axioms blank_no_u5_residual_m8w_w1021
#print axioms blank_no_u5_B_s_m8w_w1021
#print axioms blank_no_u5_A_s_m8w_w1021
#print axioms blank_no_high_m0_u5_w1021
#print axioms every_w1021_residual_has_unreachable_root

end BB6.Agent4U5SourceOnlyHighStopW1021
