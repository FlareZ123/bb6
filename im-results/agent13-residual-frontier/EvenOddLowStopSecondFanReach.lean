import EvenOddLowStopSecondFanSource
import EvenOddLowStopEvenReachIff
import OddOddLowVal
import EvenRightSixOrbit
import One307Source
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowSecondFan
open BB6.Agent46

/-- Exact blank-root reachability decomposition for the second-generation
    target P. A root hit occurs iff the direct affine parent is hit, or
    one of the source-exact odd-depth high-bounce parents is hit. -/
theorem second_parent_reach_iff
    (s u : Nat)
    (hu : u+12*s+1=2^(2048*s+129)) :
    BB6.Agent3.CReach (173*u+24) ((339*u+47)/2) ↔
      BB6.Agent3.CReach
        (173*u+24+((339*u+47)/2)-2)
        (((339*u+47)/2-2)/2) ∨
      (∃ n a k, secondHighParentCondition s u n a k ∧
        BB6.Agent3.CReach a k) := by
  have ⟨hxLarge,hyLarge,hyEven,hxyOdd⟩ :=
    second_parent_facts s u hu
  constructor
  · intro hr
    obtain ⟨a,k,hpre,hedge⟩ :=
      BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
        (173*u+24) ((339*u+47)/2) hxLarge hr
    rcases (second_parent_source_parent_iff s u a k hu).mp hedge with
      hdir | ⟨n,hcond⟩
    · rcases hdir with ⟨ha,hk⟩
      left
      rw [ha,hk] at hpre
      exact hpre
    · exact Or.inr ⟨n,a,k,hcond,hpre⟩
  · rintro (hdir | ⟨n,a,k,hcond,hrparent⟩)
    · rcases hdir with ⟨time,ht⟩
      have hedge : secNext
          (173*u+24+((339*u+47)/2)-2,(((339*u+47)/2)-2)/2) =
            some (173*u+24,(339*u+47)/2) :=
        (second_parent_source_parent_iff s u
          (173*u+24+((339*u+47)/2)-2)
          ((((339*u+47)/2)-2)/2) hu).mpr
            (Or.inl ⟨rfl,rfl⟩)
      exact ⟨time+1,by simpa [BB6.Agent8Section.run,ht] using hedge⟩
    · rcases hrparent with ⟨time,ht⟩
      have hedge : secNext (a,k)=some (173*u+24,(339*u+47)/2) :=
        (second_parent_source_parent_iff s u a k hu).mpr
          (Or.inr ⟨n,hcond⟩)
      exact ⟨time+1,by simpa [BB6.Agent8Section.run,ht] using hedge⟩

#print axioms second_parent_reach_iff

/-- For every even low-stop index z=2s, the original target R_u
    has an exact root-reachability decomposition through the unique
    first parent P and the complete second-generation source fan. -/
theorem low_ray_even_z_second_parent_fan_reach_iff
    (s u : Nat)
    (hu : u+12*s+1=2^(2048*s+129)) :
    BB6.Agent3.CReach (180*u+28) (166*u+25) ↔
      BB6.Agent3.CReach
        (173*u+24+((339*u+47)/2)-2)
        (((339*u+47)/2-2)/2) ∨
      (∃ n a k, secondHighParentCondition s u n a k ∧
        BB6.Agent3.CReach a k) := by
  have hfirstExp : 1024*(2*s)+129=2048*s+129 := by omega
  have hu' : u+6*(2*s)+1=2^(1024*(2*s)+129) := by
    rw [hfirstExp]
    exact hu
  have hfirst :=
    BB6.Agent13LowEvenIff.even_low_ray_reach_iff_unique_parent
      (2*s) u hu' (by omega)
  exact hfirst.trans (second_parent_reach_iff s u hu)

/-- For z=8r+6 with odd r, the original low-stop target is reduced
    exactly to two candidate blank-root ancestors: the direct parent
    and the unique possible high-bounce parent at depth one. -/
theorem low_ray_z14_second_fan_reach_iff
    (r u : Nat)
    (hu : u+12*(4*r+3)+1=2^(2048*(4*r+3)+129))
    (hr : r%2=1) :
    BB6.Agent3.CReach (180*u+28) (166*u+25) ↔
      BB6.Agent3.CReach
        (173*u+24+((339*u+47)/2)-2)
        (((339*u+47)/2-2)/2) ∨
      (∃ a k, secondHighParentCondition (4*r+3) u 1 a k ∧
        BB6.Agent3.CReach a k) := by
  have hsecond :=
    low_ray_even_z_second_parent_fan_reach_iff (4*r+3) u hu
  constructor
  · intro hrRoot
    rcases hsecond.mp hrRoot with hdir | ⟨n,a,k,hcond,hreach⟩
    · exact Or.inl hdir
    · have hn1 :=
        second_high_parent_depth_one_of_odd_r r u n a k hu hr hcond
      subst n
      exact Or.inr ⟨a,k,hcond,hreach⟩
  · intro hparents
    exact hsecond.mpr hparents

#print axioms low_ray_z14_second_fan_reach_iff
#print axioms second_parent_reach_iff
#print axioms low_ray_z14_second_fan_reach_iff
namespace BB6.Agent13LowSecondFan

/-- On the residual subfamily s=4r+3 with odd r, the unique
    depth-one high-bounce parent in the second-generation fan is
    forbidden by the original blank odd-image invariant.  Thus the
    complete source fan collapses to its direct affine parent. -/
theorem second_high_parent_odd_r_unreachable
    (r u n a k : Nat)
    (hu : u+12*(4*r+3)+1=2^(2048*(4*r+3)+129))
    (hr : r%2=1)
    (hcond : secondHighParentCondition (4*r+3) u n a k) :
    ¬ BB6.Agent3.CReach a k := by
  have hn1 :=
    second_high_parent_depth_one_of_odd_r r u n a k hu hr hcond
  subst n
  rcases hcond with ⟨_,haodd,ha3,hregion,hmass,hcost⟩
  have hs7 : (4*r+3)%8=7 := by omega
  have hpow32 : 32∣(2:Nat)^(2048*(4*r+3)+129) := by
    have hh : (2:Nat)^5∣2^(2048*(4*r+3)+129) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^5=32 by decide] using hh
  have hdiv32 : 32∣u+12*(4*r+3)+1 := by
    rw [hu]
    exact hpow32
  have hu32 : u%32=11 := by
    have hm := Nat.mod_eq_zero_of_dvd hdiv32
    omega
  have hX32 : (173*u+24)%32=7 := by omega
  have hYnum32 : (339*u+47)%32=0 := by omega
  have hYdiv32 : 32∣339*u+47 :=
    Nat.dvd_of_mod_eq_zero hYnum32
  rcases hYdiv32 with ⟨q,hq⟩
  have hYeq : (339*u+47)/2=16*q := by omega
  have hY16 : ((339*u+47)/2)%16=0 := by rw [hYeq]; omega
  have hmass4 :
      173*u+25+(339*u+47)/2=4*(a+3) := by
    simpa using hmass
  have ha8 : a%8=7 := by omega
  have hcost' :
      2*k+a+10=173*u+24+2*((339*u+47)/2) := by
    simpa using hcost
  have hk4 : k%4=3 := by omega
  have hkge : 5≤k := by omega
  have hsum : (a+k)%4=2 := by omega
  exact BB6.Agent13TwoParent.odd_forbidden_image a k hkge
    (by omega) (Or.inr hsum)

/-- For z=8r+6 with odd r, the complete second-generation fan
    and the odd-image invariant leave only the direct affine parent.
    This is an exact all-time blank-root reachability equivalence. -/
theorem low_ray_z14_second_fan_reach_iff_direct_parent
    (r u : Nat)
    (hu : u+12*(4*r+3)+1=2^(2048*(4*r+3)+129))
    (hr : r%2=1) :
    BB6.Agent3.CReach (180*u+28) (166*u+25) ↔
    BB6.Agent3.CReach
      (173*u+24+((339*u+47)/2)-2)
      (((339*u+47)/2-2)/2) := by
  have hfan := low_ray_z14_second_fan_reach_iff r u hu hr
  constructor
  · intro hroot
    rcases hfan.mp hroot with hdirect | ⟨n,a,k,hcond,hparent⟩
    · exact hdirect
    · exact False.elim
        (second_high_parent_odd_r_unreachable r u n a k hu hr hcond hparent)
  · intro hdirect
    exact hfan.mpr (Or.inl hdirect)

#print axioms second_high_parent_odd_r_unreachable
#print axioms low_ray_z14_second_fan_reach_iff_direct_parent


/-- Elementary lower bound used only to show the source-derived
    counters in this residual ray are large enough for the inverse lemmas. -/
private theorem second_fan_linear_le_power (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- The residual z=14 (mod 64) ray is blank-unreachable.  The proof
    composes the exact second-generation fan, the odd/odd low-valuation
    inverse, the six-residue even-right inverse, and the original
    odd-right image obstruction. -/
theorem low_ray_z14_mod64_unreachable
    (t u : Nat)
    (hu : u+6*(64*t+14)+1=2^(1024*(64*t+14)+129)) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  have hmassRel : 12*(32*t+7)=6*(64*t+14) := by omega
  have hpowRel : 2048*(32*t+7)+129=1024*(64*t+14)+129 := by omega
  have hu' : u+12*(32*t+7)+1=2^(2048*(32*t+7)+129) := by
    rw [hmassRel,hpowRel]
    exact hu
  have hr : (8*t+1)%2=1 := by omega
  let X := 173*u+24
  let Y := (339*u+47)/2
  let Dx := X+Y-2
  let Dy := (Y-2)/2
  let Ex := (1709*u+209)/8
  let Ey := (2387*u+271)/16
  let Fx := Ex+Ey-2
  let Fy := (Ey-2)/2
  intro hroot
  have hDreach : BB6.Agent3.CReach Dx Dy := by
    have hiff := low_ray_z14_second_fan_reach_iff_direct_parent
      (8*t+1) u hu' hr
    have hh := hiff.mp hroot
    simpa [Dx,Dy,X,Y] using hh
  have hlin : 2048*(32*t+7)+130≤2^(2048*(32*t+7)+129) :=
    second_fan_linear_le_power _
  rw [←hu'] at hlin
  have huLarge : 129≤u := by omega
  have hpow128 : 128∣2^(2048*(32*t+7)+129) := by
    have hh : (2:Nat)^7∣2^(2048*(32*t+7)+129) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^7=128 by decide] using hh
  have hdiv128 : 128∣u+12*(32*t+7)+1 := by
    rw [hu']
    exact hpow128
  have hu128 : u%128=43 := by
    have hm := Nat.mod_eq_zero_of_dvd hdiv128
    omega
  have hu32 : u%32=11 := by omega
  have hnum2 : (339*u+47)%2=0 := by omega
  have hY2 : 2*Y=339*u+47 := by
    dsimp [Y]
    have hh := Nat.mod_add_div (339*u+47) 2
    omega
  have hDxEq : Dx=(685*u+91)/2 := by
    dsimp [Dx,X,Y]
    omega
  have hDyEq : Dy=(339*u+43)/4 := by
    dsimp [Dy,Y]
    omega
  have hDsumEq : Dx+Dy=(1709*u+225)/4 := by
    rw [hDxEq,hDyEq]
    omega
  have hsum8 : (Dx+Dy)%8=4 := by
    rw [hDsumEq]
    omega
  have hDxOdd : Dx%2=1 := by rw [hDxEq]; omega
  have hDyOdd : Dy%2=1 := by rw [hDyEq]; omega
  have hDy5 : 5≤Dy := by rw [hDyEq]; omega
  have h4 : (Dx+Dy)%4=0 := by omega
  have h16 : (Dx+Dy)%16≠0 := by omega
  have hsize : 24≤Dx+Dy := by rw [hDsumEq]; omega
  have hDparent :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff
      Dx Dy hDxOdd hDyOdd hDy5 h4 h16 hsize).mp hDreach
  have hE1 : (Dx+Dy-4)/2=Ex := by
    rw [hDsumEq]
    dsimp [Ex]
    omega
  have hD3 : Dx+3*Dy-10=(2387*u+271)/4 := by
    rw [hDxEq,hDyEq]
    omega
  have hE2 : (Dx+3*Dy-10)/4=Ey := by
    rw [hD3]
    dsimp [Ey]
    omega
  have hEreach : BB6.Agent3.CReach Ex Ey := by
    simpa only [BB6.Agent3.CReach,hE1,hE2] using hDparent
  have hEx16 : Ex%16=12 := by dsimp [Ex]; omega
  have hEy8 : Ey%8=0 := by dsimp [Ey]; omega
  have hEy6 : 6≤Ey := by dsimp [Ey]; omega
  have hEyEven : Ey%2=0 := by omega
  have hEsum8 : (Ex+Ey)%8=4 := by omega
  have hFreach : BB6.Agent3.CReach Fx Fy := by
    have hiff := BB6.Agent46.six_even_right_blank_reach_iff
      Ex Ey hEy6 hEyEven (by omega) (by omega)
    have hh := hiff.mp hEreach
    simpa [Fx,Fy] using hh
  have hFy4 : Fy%4=3 := by dsimp [Fy]; omega
  have hFy5 : 5≤Fy := by dsimp [Fy]; omega
  have hFyOdd : Fy%2=1 := by omega
  have hFsum4 : (Fx+Fy)%4=1 := by dsimp [Fx,Fy]; omega
  exact (BB6.Agent13TwoParent.odd_forbidden_image
    Fx Fy hFy5 hFyOdd (Or.inl hFsum4)) hFreach

/-- The genuine low-stop equation m=512z+67 transfers z=14 (mod 64)
    to the residual root R_u with u satisfying the exact power relation
    above.  This is a complete all-time exclusion of that stopping
    progression, not a finite simulation claim. -/
theorem low_stop_m67_z14_mod64_unreachable
    (z m k : Nat)
    (hm : m=512*z+67)
    (hz : z%64=14)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 32768∣2^(2*m+3) := by
    have hh : (2:Nat)^15∣2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^15=32768 by decide] using hh
  have hpmod : (2^(2*m+3))%32768=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  let t := z/64
  have hzEq : z=64*t+14 := by
    have hh := Nat.mod_add_div z 64
    dsimp [t]
    omega
  have hkmod : k%32768=11059 := by
    have hs : (k+3*m+4)%32768=0 := by
      rw [hstop]
      exact hpmod
    rw [hm,hzEq] at hs
    omega
  let u := 128*(k/32768)+43
  have hu128 : u%128=43 := by
    dsimp [u]
    have hh := Nat.mod_add_div k 32768
    rw [hkmod] at hh
    omega
  have hk : k=256*u+51 := by
    dsimp [u]
    have hh := Nat.mod_add_div k 32768
    rw [hkmod] at hh
    omega
  have hexp : 2*m+3=1024*z+137 := by rw [hm]; omega
  have hpow : 2^(2*m+3)=256*2^(1024*z+129) := by
    rw [hexp]
    rw [show 1024*z+137=(1024*z+129)+8 by omega,Nat.pow_add]
    rw [show (2:Nat)^8=256 by decide]
    exact Nat.mul_comm _ _
  have hstop' := hstop
  rw [hpow,hk,hm,hzEq] at hstop'
  have hu : u+6*(64*t+14)+1=2^(1024*(64*t+14)+129) := by
    dsimp [t] at *
    omega
  intro hr
  have hR := BB6.Agent13One307.four_step_to_rectangle u hr
  exact low_ray_z14_mod64_unreachable t u hu hR

#print axioms low_ray_z14_mod64_unreachable
#print axioms low_stop_m67_z14_mod64_unreachable

end BB6.Agent13LowSecondFan
