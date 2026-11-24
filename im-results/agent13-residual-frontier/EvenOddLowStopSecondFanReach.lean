import EvenOddLowStopSecondFanSource
import EvenOddLowStopEvenReachIff
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
end BB6.Agent13LowSecondFan


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
