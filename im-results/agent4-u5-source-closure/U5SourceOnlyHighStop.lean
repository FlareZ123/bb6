import U5Q0SourceOnly
import U5Y3M8
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000

/-!
Source-only end-to-end closure of the frozen U5 high-m=0 cylinder
w=21 (mod 32). The q=0 branch is discharged by the exact source-only
predecessor proof in U5Q0SourceOnly; no finite quotient certificate
is imported anywhere in this dependency chain.
-/

namespace BB6.Agent4U5SourceOnlyHighStop
open BB6.Agent3
open BB6.Agent3U5DepthFan

private theorem succ_le_two_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpow : 2^(n+1)=2^n*2 := by rw [Nat.pow_succ]
    omega

private theorem u5_q1_parent_unreachable (p : Nat)
    (hp8 : p%8=1) (hpge : 3≤p) :
    ¬ CReach (2*p-3) (7*p-4) := by
  apply BB6.Agent11High.blank_no_odd_sum_two
  · omega
  · omega
  · omega


/-- The U5 residual equations are nonempty for every w. Fermat's
little theorem is reduced to the two concrete residues
2^210=1 and 2^201=68 (mod 211); the elementary bound
2^r≥r+1 then gives s≥27w+1 and m≥24w. -/
theorem u5_residual_nonempty (w : Nat) :
    ∃ s m,
      211*s+129=5*2^(201+3360*w) ∧
      32*s=32+840*w+m := by
  let r := 201+3360*w
  have h210 : (2:Nat)^210%211=1 := by decide
  have h201 : (2:Nat)^201%211=68 := by decide
  have h210pow : ((2:Nat)^210)^(16*w)%211=1 := by
    rw [Nat.pow_mod,h210]
    simp
  have hpow : (2:Nat)^r%211=68 := by
    dsimp [r]
    rw [show 201+3360*w=201+210*(16*w) by omega,
      Nat.pow_add,Nat.pow_mul,Nat.mul_mod,h201,h210pow]
    decide
  have hmod : (5*2^r)%211=129 := by
    rw [Nat.mul_mod,hpow]
    decide
  let s := 5*2^r/211
  have hdecomp := Nat.mod_add_div (5*2^r) 211
  have hs : 211*s+129=5*2^r := by
    dsimp [s]
    rw [hmod] at hdecomp
    omega
  have hrpow : r+1≤2^r := succ_le_two_pow r
  have hlin : 211*(27*w+1)+129≤5*(r+1) := by
    dsimp [r]
    omega
  have hbig : 211*(27*w+1)+129≤5*2^r :=
    le_trans hlin (Nat.mul_le_mul_left 5 hrpow)
  have hsge : 27*w+1≤s := by
    dsimp [s]
    omega
  let m := 32*s-32-840*w
  have hm : 32*s=32+840*w+m := by
    dsimp [m]
    omega
  exact ⟨s,m,by simpa [r] using hs,hm⟩


/-- The residual equations determine s strictly increasingly with w;
this makes the constructed w=32*n+21 root sequence pairwise distinct. -/
theorem u5_residual_s_strict_mono
    (w1 w2 s1 s2 : Nat) (hw : w1<w2)
    (hs1 : 211*s1+129=5*2^(201+3360*w1))
    (hs2 : 211*s2+129=5*2^(201+3360*w2)) :
    s1<s2 := by
  have hr : 201+3360*w1 < 201+3360*w2 := by omega
  have hpow : 2^(201+3360*w1) < 2^(201+3360*w2) :=
    Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) hr
  omega

/-- The y=3 terminal of the U5 M8 residual is unreachable on
w=21 (mod 32). The q=0 parent is excluded by the source-only
t=19 (mod 32) inverse fan; q=1 is odd-right sum-two; q>=2
contradicts m+1=1 (mod 8). -/
theorem blank_no_u5_residual_m8w_w21 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%32=21) :
    ¬ CReach (302+512*s-4*(201+3360*w)) 3 := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  have hm' : 32*s=32+105*(8*w)+m := by omega
  have hm8 : m%8=0 := by
    have hmod : (32*s)%8=(32+840*w+m)%8 := by rw [hm]
    have hleft : (32*s)%8=0 := by simp [Nat.mul_mod]
    have hright : (32+840*w+m)%8=m%8 := by simp [Nat.add_mod,Nat.mul_mod]
    rw [hleft,hright] at hmod
    exact hmod.symm
  have hp8 : (m+1)%8=1 := by simp [Nat.add_mod,hm8]
  have hrpow : 201+3360*w+1≤2^(201+3360*w) := succ_le_two_pow _
  have hlin : 211*(27*w+1)+129≤5*(201+3360*w+1) := by omega
  have hbig : 211*(27*w+1)+129≤5*2^(201+3360*w) := by omega
  have hsge : 27*w+1≤s := by omega
  have hmge : 24*w≤m := by omega
  have hwge : 21≤w := by omega
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
            exact BB6.Agent4U5SourceOnly.blank_no_u5_q0_parent_w21
              w s m t hs hm hp hw htpos hparent
          · by_cases hq1 : q=1
            · subst q
              have hUeq : U=m+1 := by simpa using hdecomp.symm
              have haEq : a=2*(m+1)-3 := by omega
              have hkEq : k=7*(m+1)-4 := by omega
              have hparent : CReach (2*(m+1)-3) (7*(m+1)-4) := by
                rw [haEq,hkEq] at hr
                exact ⟨n,hr⟩
              exact u5_q1_parent_unreachable (m+1) hp8 hpge hparent
            · have hq2 : 2≤q := by omega
              have h4pow : 4∣2^(2*q-2) := by
                change 2^2∣2^(2*q-2)
                exact Nat.pow_dvd_pow 2 (by omega)
              rcases h4pow with ⟨r,hrpow⟩
              have h4 : 4∣m+1 := by
                refine ⟨r*U, ?_⟩
                rw [hdecomp,hrpow]
                ac_rfl
              have h4mod : (m+1)%4=0 := Nat.mod_eq_zero_of_dvd h4
              omega

/-- The B_s feeder of the high m=0 stop is unreachable on this cylinder. -/
theorem blank_no_u5_B_s_m8w_w21 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%32=21) :
    ¬ CReach (54+90*s) (127+211*s) := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  intro hB
  have hterminal :=
    (BB6.Agent3U5M8.u5_residual_six_even_right_chain (8*w) s hs').mp hB
  have hM : 201+420*(8*w)=201+3360*w := by omega
  have hterminal' : CReach (302+512*s-4*(201+3360*w)) 3 := by
    simpa only [hM] using hterminal
  exact blank_no_u5_residual_m8w_w21 w s m hs hm hw hterminal'

/-- Both exact source parents of A_s are excluded, closing the full
A_s branch on w=21 (mod 32). -/
theorem blank_no_u5_A_s_m8w_w21 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%32=21) :
    ¬ CReach (130+208*s) (94+152*s) := by
  have hdiv : 8∣2^(201+3360*w) := by
    change 2^3∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod : (2^(201+3360*w))%8=0 := Nat.mod_eq_zero_of_dvd hdiv
  have hsmod : (211*s+129)%8=0 := by
    rw [hs,Nat.mul_mod,hpowmod]
  have hs8 : s%8=5 := by omega
  have hL := BB6.Agent11M0SumZeroVerified.blank_no_L_s_mod8_five s hs8
  have hB := blank_no_u5_B_s_m8w_w21 w s m hs hm hw
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
U5 residual family w=21 (mod 32), using only exact source
predecessors and the authentic blank-section orbit. -/
theorem blank_no_high_m0_u5_w21 (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%32=21) :
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
  exact blank_no_u5_A_s_m8w_w21 w s m hs hm hw hA'

/-- The residual equation fixes the high m=0 root's parameter
residue: s=293 (mod512), hence j=39+64*s=18791 (mod32768)
and t=(j-7)/32=587 (mod1024). This is disjoint from the four
previously source-certified m=0 high-stop classes. -/
theorem u5_high_root_parameter_residue (w s : Nat)
    (hs : 211*s+129=5*2^(201+3360*w)) :
    (39+64*s)%32768=18791 ∧ (1+2*s)%1024=587 := by
  have hdiv : 512∣2^(201+3360*w) := by
    change 2^9∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod : (2^(201+3360*w))%512=0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  have hmod : (211*s+129)%512=0 := by
    rw [hs,Nat.mul_mod,hpowmod]
    simp
  have hsmod : s%512=293 := by omega
  constructor <;> omega

/-- Explicit infinite nonvacuity of the source-only root exclusion:
for every n, the w=32*n+21 residual equations have a natural
solution s,m, and the corresponding high m=0 stopping root is
blank-unreachable in the new residue j=18791 (mod32768). -/
theorem every_w21_residual_has_unreachable_root (n : Nat) :
    ∃ s m,
      211*s+129=5*2^(201+3360*(32*n+21)) ∧
      32*s=32+840*(32*n+21)+m ∧
      (39+64*s)%32768=18791 ∧
      ¬ CReach (2*(39+64*s)+3) (3*(39+64*s)+7) := by
  obtain ⟨s,m,hs,hm⟩ := u5_residual_nonempty (32*n+21)
  have hw : (32*n+21)%32=21 := by omega
  have hroot := blank_no_high_m0_u5_w21 (32*n+21) s m hs hm hw
  have hres := u5_high_root_parameter_residue (32*n+21) s hs
  exact ⟨s,m,hs,hm,hres.1,hroot⟩

#print axioms u5_residual_nonempty
#print axioms u5_residual_s_strict_mono
#print axioms u5_high_root_parameter_residue
#print axioms blank_no_u5_residual_m8w_w21
#print axioms blank_no_u5_B_s_m8w_w21
#print axioms blank_no_u5_A_s_m8w_w21
#print axioms blank_no_high_m0_u5_w21
#print axioms every_w21_residual_has_unreachable_root

end BB6.Agent4U5SourceOnlyHighStop
