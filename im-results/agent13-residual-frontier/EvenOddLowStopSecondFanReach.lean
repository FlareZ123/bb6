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

private theorem second_fan_linear_le_power (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- On the subfamily s=64t+7, every high-bounce parent in the
    second-generation fan has depth one and is itself blank-unreachable.
    Its unique odd/odd low-valuation predecessor has even/odd coordinates
    with sum 1 modulo four, contradicting the original odd-image invariant. -/
theorem second_high_parent_r16_one_unreachable
    (t u n a k : Nat)
    (hu : u+12*(64*t+7)+1=2^(2048*(64*t+7)+129))
    (hcond : secondHighParentCondition (64*t+7) u n a k) :
    ¬ BB6.Agent3.CReach a k := by
  have hr : (16*t+1)%2=1 := by omega
  have hsEq : 4*(16*t+1)+3=64*t+7 := by omega
  have huR :
      u+12*(4*(16*t+1)+3)+1 =
        2^(2048*(4*(16*t+1)+3)+129) := by
    rw [hsEq]
    exact hu
  have hn1 :=
    second_high_parent_depth_one_of_odd_r (16*t+1) u n a k
      huR hr (by simpa [hsEq] using hcond)
  subst n
  rcases hcond with ⟨_,haodd,ha3,hregion,hmass,hcost⟩
  have hlin : 2048*(64*t+7)+130 ≤
      2^(2048*(64*t+7)+129) :=
    second_fan_linear_le_power _
  have huLarge : 129≤u := by omega
  have hp256 : (256:Nat)∣2^(2048*(64*t+7)+129) := by
    have hh : (2:Nat)^8∣2^(2048*(64*t+7)+129) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^8=256 by decide] using hh
  have hdiv256 : 256∣u+12*(64*t+7)+1 := by
    rw [hu]
    exact hp256
  have hmod256 := Nat.mod_eq_zero_of_dvd hdiv256
  have hu256 : u%256=171 := by omega
  have hu128 : u%128=43 := by omega
  have hu32 : u%32=11 := by omega
  have hnumEven : (339*u+47)%2=0 := by omega
  have hY2 : 2*((339*u+47)/2)=339*u+47 := by
    have hh := Nat.mod_add_div (339*u+47) 2
    omega
  have hmass' :
      173*u+25+(339*u+47)/2=4*(a+3) := by
    simpa using hmass
  have hcost' :
      2*k+a+10=173*u+24+2*((339*u+47)/2) := by
    simpa using hcost
  have haEq : 8*a=685*u+73 := by omega
  have hkEq : 16*k=3411*u+415 := by omega
  have hkOdd : k%2=1 := by omega
  have hsumEq : 16*(a+k)=4781*u+561 := by omega
  have hres64 : (4781*u+561)%64=0 := by omega
  have hdiv64 : 64∣16*(a+k) := by
    rw [hsumEq]
    exact Nat.dvd_of_mod_eq_zero hres64
  have hdiv4 : 4∣a+k := by
    rcases hdiv64 with ⟨q,hq⟩
    refine ⟨q,?_⟩
    omega
  have hsum4 : (a+k)%4=0 :=
    Nat.mod_eq_zero_of_dvd hdiv4
  have hsum16 : (a+k)%16≠0 := by
    intro hzero
    have hd16 : 16∣a+k := Nat.dvd_of_mod_eq_zero hzero
    rcases hd16 with ⟨q,hq⟩
    have hd256 : 256∣16*(a+k) := by
      refine ⟨q,?_⟩
      rw [hq]
      omega
    rw [hsumEq] at hd256
    have hzero' := Nat.mod_eq_zero_of_dvd hd256
    have hres256 : (4781*u+561)%256=192 := by omega
    omega
  have hsize : 24≤a+k := by omega
  let x1 := (a+k-4)/2
  let y1 := (a+3*k-10)/4
  have hXeq : x1=(4781*u+497)/32 := by
    dsimp [x1]
    omega
  have hYeq : y1=(11603*u+1231)/64 := by
    dsimp [y1]
    omega
  have hx1mod4 : x1%4=0 := by rw [hXeq]; omega
  have hy1mod4 : y1%4=1 := by rw [hYeq]; omega
  have hy1odd : y1%2=1 := by omega
  have hy1large : 5≤y1 := by rw [hYeq]; omega
  have hsum1 : (x1+y1)%4=1 := by omega
  intro hreach
  have hreach1 : BB6.Agent3.CReach x1 y1 :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff
      a k haodd hkOdd (by omega) hsum4 hsum16 hsize).mp hreach
  exact BB6.Agent13TwoParent.odd_forbidden_image
    x1 y1 hy1large hy1odd (Or.inl hsum1) hreach1

/-- For z=8r+6 with r=16t+1, the complete second-generation fan
    and the odd-image invariant leave only the direct affine parent.
    This is an exact all-time blank-root reachability equivalence. -/
theorem low_ray_z14_second_fan_reach_iff_direct_parent_r16_one
    (t u : Nat)
    (hu : u+12*(64*t+7)+1=2^(2048*(64*t+7)+129)) :
    BB6.Agent3.CReach (180*u+28) (166*u+25) ↔
    BB6.Agent3.CReach
      (173*u+24+((339*u+47)/2)-2)
      (((339*u+47)/2-2)/2) := by
  have hr : (16*t+1)%2=1 := by omega
  have hsEq : 4*(16*t+1)+3=64*t+7 := by omega
  have huR :
      u+12*(4*(16*t+1)+3)+1 =
        2^(2048*(4*(16*t+1)+3)+129) := by
    rw [hsEq]
    exact hu
  have hfan :=
    low_ray_z14_second_fan_reach_iff (16*t+1) u huR hr
  constructor
  · intro hroot
    rcases hfan.mp hroot with hdirect | ⟨a,k,hcond,hparent⟩
    · exact hdirect
    · exact False.elim
        (second_high_parent_r16_one_unreachable t u 1 a k hu
          (by simpa [hsEq] using hcond) hparent)
  · intro hdirect
    exact hfan.mpr (Or.inl hdirect)



/-- The residual z=14 (mod 128) ray is blank-unreachable.  The
    direct second-generation parent is forced through the odd/odd
    low-valuation inverse and then the six-residue even-right inverse;
    the remaining depth-one high parent was excluded above. -/
theorem low_ray_z14_mod128_unreachable
    (t u : Nat)
    (hu : u+6*(128*t+14)+1=2^(1024*(128*t+14)+129)) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  have hmassRel : 12*(64*t+7)=6*(128*t+14) := by omega
  have hpowRel : 2048*(64*t+7)+129=1024*(128*t+14)+129 := by omega
  have hu' : u+12*(64*t+7)+1=2^(2048*(64*t+7)+129) := by
    rw [hmassRel,hpowRel]
    exact hu
  have hiff :=
    low_ray_z14_second_fan_reach_iff_direct_parent_r16_one t u hu'
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
    have hh := hiff.mp hroot
    simpa [Dx,Dy,X,Y] using hh
  have hlin : 2048*(64*t+7)+130≤2^(2048*(64*t+7)+129) :=
    second_fan_linear_le_power _
  rw [←hu'] at hlin
  have huLarge : 129≤u := by omega
  have hpow128 : 128∣2^(2048*(64*t+7)+129) := by
    have hh : (2:Nat)^7∣2^(2048*(64*t+7)+129) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^7=128 by decide] using hh
  have hdiv128 : 128∣u+12*(64*t+7)+1 := by
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



/-- The genuine low-stop equation m=512z+67 transfers z=14 (mod 128)
    to the residual root R_u with u satisfying the exact power relation.
    This is a complete all-time exclusion of that stopping progression. -/
theorem low_stop_m67_z14_mod128_unreachable
    (z m k : Nat)
    (hm : m=512*z+67)
    (hz : z%128=14)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 65536∣2^(2*m+3) := by
    have hh : (2:Nat)^16∣2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^16=65536 by decide] using hh
  have hpmod : (2^(2*m+3))%65536=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  let t := z/128
  have hzEq : z=128*t+14 := by
    have hh := Nat.mod_add_div z 128
    dsimp [t]
    omega
  have hkmod : k%65536=43827 := by
    have hs : (k+3*m+4)%65536=0 := by
      rw [hstop]
      exact hpmod
    rw [hm,hzEq] at hs
    omega
  let u := 256*(k/65536)+171
  have hu256 : u%256=171 := by
    dsimp [u]
    have hh := Nat.mod_add_div k 65536
    rw [hkmod] at hh
    omega
  have hk : k=256*u+51 := by
    dsimp [u]
    have hh := Nat.mod_add_div k 65536
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
  have hu : u+6*(128*t+14)+1=2^(1024*(128*t+14)+129) := by
    omega
  intro hr
  have hr' : BB6.Agent3.CReach 1 (256*u+51) := by
    simpa [hk] using hr
  have hR := BB6.Agent13One307.four_step_to_rectangle u hr'
  exact low_ray_z14_mod128_unreachable t u hu hR

#print axioms low_ray_z14_mod128_unreachable
#print axioms low_stop_m67_z14_mod128_unreachable

end BB6.Agent13LowSecondFan
