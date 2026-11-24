import AffineConeKernel
import Root32Precision
import Root32ShadowRoot
import StopModShadow
import Root32HighStopP7
import Root32HighStopIndexMap
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

namespace BB6.Agent19Root32Cone
open BB6.Agent13AffineCone
open BB6.Agent46
open BB6.Agent3Root32HighStopIntegrated (RunReach run_parent_of_left_gt5)

/-- Specialize the already sound, complete-parent affine-cone checker to
    the literal blank-section run of the corrected root32 reduction. -/
theorem run_cone_excluded (f : Nat) (ray : Ray) (h : excluded f ray=true)
    (s : Nat) : ¬RunReach (ray.x.eval s) (ray.y.eval s) := by
  apply excluded_sound RunReach ?_ ?_ f ray h s
  · intro x y hx hy hr
    obtain ⟨a,k,hp,hedge⟩ := run_parent_of_left_gt5 x y hx hr
    exact ⟨a,k,hp,(complete_section_inverse a k x y (by omega)).mp hedge⟩
  · intro x y hy ho hs hr
    rcases hr with ⟨n,hn⟩
    cases n with
    | zero => simp [BB6.Agent8Section.run] at hn; omega
    | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n x y hn hy ho
      omega

def residualRay (ax bx ay by_ b m : Nat) : Ray :=
  ⟨⟨ax*m,ax*b+bx⟩,⟨ay*m,ay*b+by_⟩⟩

@[simp] theorem residualRay_x (ax bx ay by_ b m s : Nat) :
    (residualRay ax bx ay by_ b m).x.eval s=ax*(b+m*s)+bx := by
  simp [residualRay,Linear.eval,Nat.mul_add,Nat.mul_assoc]
  omega

@[simp] theorem residualRay_y (ax bx ay by_ b m s : Nat) :
    (residualRay ax bx ay by_ b m).y.eval s=ay*(b+m*s)+by_ := by
  simp [residualRay,Linear.eval,Nat.mul_add,Nat.mul_assoc]
  omega

def d0Ray (b m : Nat) : Ray :=
  residualRay 1469153280 393975148 2788638720 747814654 b m

def lRay (b m : Nat) : Ray :=
  residualRay 5065196640 1358307257 990617040 265648583 b m

def pRay (b m : Nat) : Ray :=
  residualRay 1376399640 369101882 2835015540 760251268 b m

def threeExcluded (f b m : Nat) : Bool :=
  excluded f (d0Ray b m) && excluded f (lRay b m) && excluded f (pRay b m)

/-- All three corrected residuals are discharged simultaneously,
    without assuming the erroneous old two-residual reduction. -/
theorem three_excluded_sound (f b m s : Nat) (h : threeExcluded f b m=true) :
    ¬(RunReach (1469153280*(b+m*s)+393975148) (2788638720*(b+m*s)+747814654) ∨
      RunReach (5065196640*(b+m*s)+1358307257) (990617040*(b+m*s)+265648583) ∨
      RunReach (1376399640*(b+m*s)+369101882) (2835015540*(b+m*s)+760251268)) := by
  simp only [threeExcluded,Bool.and_eq_true] at h
  intro hr
  rcases hr with hd | hl | hp
  · exact (run_cone_excluded f (d0Ray b m) h.1.1 s) (by simpa [d0Ray] using hd)
  · exact (run_cone_excluded f (lRay b m) h.1.2 s) (by simpa [lRay] using hl)
  · exact (run_cone_excluded f (pRay b m) h.2 s) (by simpa [pRay] using hp)

/-- Generic exact-root high-stop exclusion for any successful
    all-three-residual affine certificate. -/
theorem root32_no_highstop_of_t (r E u f b m : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hroot : 18018+211*u+22155*r=20*2^(E-13))
    (hcone : threeExcluded f b m=true)
    (hparam : ∃ s, u=1802+6720*(b+m*s)) :
    ¬RunReach (1048576*u+70538) 3 := by
  intro hT
  obtain ⟨t,hu,hr⟩ := BB6.Agent3Root32HighStopP7.root32_highstop_reduces_to_three_residuals
    r E u hr64 hE hroot hT
  obtain ⟨s,hs⟩ := hparam
  have ht : t=b+m*s := by omega
  rw [ht] at hr
  exact three_excluded_sound f b m s hcone hr

/-- Nine accepted affine cylinders selected from the prior root32 families.
    Pairs are (modulus, residue). The list is checked by kernel reduction. -/
def certificates : List (Nat × Nat) :=
  [(16,1),(2048,47),(8192,559),(256,31),(8192,7183),(8192,2575),
   (1024,159),(8192,719),(8192,7839)]

def certOK (p : Nat × Nat) : Bool :=
  decide (0<p.1 ∧ p.2<p.1 ∧ 8192%p.1=0) && threeExcluded 24 p.2 p.1

theorem certificates_checked : certificates.all certOK=true := by decide

/-- The root-index predicate uses the already proved relation
    (t+j)%8192=3780, with j=r/64. -/
def coveredJ (j : Nat) : Bool :=
  certificates.any (fun p => (j+p.2)%p.1 == 3780%p.1)

private theorem cancel_mod_right (x y j m : Nat) (hm : 0<m)
    (h : (x+j)%m=(y+j)%m) : x%m=y%m := by
  let c := m-j%m
  have hj : j%m+c=m := Nat.add_sub_of_le (Nat.le_of_lt (Nat.mod_lt _ hm))
  have hc (z : Nat) : ((z+j)%m+c)%m=z%m := by
    rw [←Nat.add_mod_mod z j m,Nat.mod_add_mod,Nat.add_assoc,hj,Nat.add_mod_right]
  exact (hc x).symm.trans ((congrArg (fun z => (z+c)%m) h).trans (hc y))

/-- All-time exclusion of the actual high-stop target, for the certified
    root-index union. No bound is imposed on the blank orbit or j. -/
theorem root32_no_highstop (r E u : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hroot : 18018+211*u+22155*r=20*2^(E-13))
    (hc : coveredJ (r/64)=true) : ¬RunReach (1048576*u+70538) 3 := by
  intro hT
  obtain ⟨t,hu,hr⟩ := BB6.Agent3Root32HighStopP7.root32_highstop_reduces_to_three_residuals
    r E u hr64 hE hroot hT
  let j := r/64
  have hrj : r=32+64*j := by
    have he := Nat.mod_add_div r 64
    rw [hr64] at he
    exact he.symm
  have hE30 : 30≤E := by omega
  have heq := BB6.Agent3Root32HighStopIndexMap.root32_original_to_tj u r t j E hE30 hu hrj hroot
  have hmod := BB6.Agent3Root32HighStopIndexMap.root32_tj_mod8192 t j E hE30 heq
  obtain ⟨p,hmem,hp⟩ := List.any_eq_true.mp hc
  have hpc := List.all_eq_true.mp certificates_checked p hmem
  simp only [certOK,Bool.and_eq_true,decide_eq_true_eq] at hpc
  obtain ⟨⟨hm,hb,hd⟩,hcone⟩ := hpc
  have hdiv : p.1 ∣ 8192 := Nat.dvd_of_mod_eq_zero hd
  have htj : (t+j)%p.1=3780%p.1 := by
    rw [←Nat.mod_mod_of_dvd (t+j) hdiv,hmod]
  have hp' : (j+p.2)%p.1=3780%p.1 := beq_iff_eq.mp hp
  have hcancel : (t+j)%p.1=(p.2+j)%p.1 := by
    rw [Nat.add_comm p.2 j,hp']; exact htj
  have ht : t%p.1=p.2 := by
    rw [cancel_mod_right t p.2 j p.1 hm hcancel,Nat.mod_eq_of_lt hb]
  have hte : t=p.2+p.1*(t/p.1) := by
    have hh := Nat.mod_add_div t p.1
    rw [ht] at hh
    exact hh.symm
  rw [hte] at hr
  exact three_excluded_sound 24 p.2 p.1 (t/p.1) hcone hr

#print axioms run_cone_excluded
#print axioms three_excluded_sound
#print axioms certificates_checked
#print axioms root32_no_highstop_of_t
#print axioms root32_no_highstop

/-- An executable exact-root exclusion at any binary precision. This is not
    restricted to the nine previously listed cylinders or modulus 8192. -/
def precisionExcluded (f p j : Nat) : Bool :=
  threeExcluded f (BB6.Agent19Root32Precision.rootResidue j p) (2^p)

theorem precisionExcluded_periodic (f p j : Nat) :
    precisionExcluded f p j=precisionExcluded f p (j%2^p) := by
  unfold precisionExcluded
  rw [← BB6.Agent19Root32Precision.rootResidue_periodic j p]

/-- Complete-source exclusion for every root whose residue is accepted
    by the all-parent certificate, at any precision p≤E-17. -/
theorem root32_no_highstop_at_precision (r E u f p : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hroot : 18018+211*u+22155*r=20*2^(E-13))
    (hp : p≤E-17)
    (hc : precisionExcluded f p (r/64)=true) :
    ¬RunReach (1048576*u+70538) 3 := by
  intro hT
  obtain ⟨t,hu,hr⟩ := BB6.Agent3Root32HighStopP7.root32_highstop_reduces_to_three_residuals
    r E u hr64 hE hroot hT
  let j := r/64
  have hrj : r=32+64*j := by
    have he := Nat.mod_add_div r 64
    rw [hr64] at he
    exact he.symm
  have heq := BB6.Agent3Root32HighStopIndexMap.root32_original_to_tj u r t j E (by omega) hu hrj hroot
  have hb := BB6.Agent19Root32Precision.rootResidue_exact t j E p hp heq
  have ht : t=BB6.Agent19Root32Precision.rootResidue j p+2^p*(t/2^p) := by
    have he := Nat.mod_add_div t (2^p)
    rw [hb] at he
    exact he.symm
  rw [ht] at hr
  exact three_excluded_sound f _ _ (t/2^p) hc hr

/-- Two previously unresolved root cylinders become provably excluded
    at precision 16, using all three residuals and all source parents. -/
theorem precision16_new_examples :
    precisionExcluded 24 16 60533=true ∧
    precisionExcluded 24 16 51765=true := by decide

theorem root32_no_highstop_precision16_examples (r E u : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hroot : 18018+211*u+22155*r=20*2^(E-13))
    (hj : (r/64)%65536=60533 ∨ (r/64)%65536=51765) :
    ¬RunReach (1048576*u+70538) 3 := by
  apply root32_no_highstop_at_precision r E u 24 16 hr64 hE hroot (by omega)
  rw [precisionExcluded_periodic]
  change precisionExcluded 24 16 ((r/64)%65536)=true
  rcases hj with hj | hj
  · rw [hj]; exact precision16_new_examples.1
  · rw [hj]; exact precision16_new_examples.2

#print axioms precisionExcluded_periodic
#print axioms root32_no_highstop_at_precision
#print axioms precision16_new_examples
#print axioms root32_no_highstop_precision16_examples

/-- Shadow search specialized to the verified, complete original source
    predecessor relation, including every ordinary high depth. -/
theorem run_shadow_excluded (f p u v x y : Nat)
    (hc : BB6.Agent19Shadow.excluded f p u v=true)
    (hl : BB6.Agent19Shadow.lift p u v x y) : ¬RunReach x y := by
  apply BB6.Agent19Shadow.excluded_sound RunReach ?_ ?_ f p u v x y hc hl
  · intro x y hy ho hs hr
    rcases hr with ⟨n,hn⟩
    cases n with
    | zero => simp [BB6.Agent8Section.run] at hn; omega
    | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n x y hn hy ho
      omega
  · intro x y w hx hy hv hq hr
    obtain ⟨a,k,hp,hedge⟩ := run_parent_of_left_gt5 x y hx hr
    have hi := (complete_section_inverse a k x y (by omega)).mp hedge
    rcases parent_equations a k x y w hy hv hq hi with hd | ⟨n,hn⟩
    · exact Or.inl ⟨a,k,hp,hd⟩
    · exact Or.inr ⟨a,k,n,hp,hn⟩

/-- Exact root32 target exclusion using compact shadow arithmetic. The
    parameter p can be much larger than machine-word size without
    materializing any modulus or enormous root coordinates. -/
theorem root32_no_highstop_shadow (r E u f p : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hroot : 18018+211*u+22155*r=20*2^(E-13))
    (hp : p≤E-17)
    (hc : BB6.Agent19Shadow.threeShadowExcluded f p (r/64)=true) :
    ¬RunReach (1048576*u+70538) 3 := by
  intro hT
  obtain ⟨t,hu,hr⟩ := BB6.Agent3Root32HighStopP7.root32_highstop_reduces_to_three_residuals
    r E u hr64 hE hroot hT
  let j := r/64
  have hrj : r=32+64*j := by
    have he := Nat.mod_add_div r 64
    rw [hr64] at he
    exact he.symm
  have heq := BB6.Agent3Root32HighStopIndexMap.root32_original_to_tj u r t j E (by omega) hu hrj hroot
  obtain ⟨hd,hl,hP⟩ := BB6.Agent19Shadow.three_shadow_lift t j (E-17) p hp heq
  simp only [BB6.Agent19Shadow.threeShadowExcluded,Bool.and_eq_true] at hc
  rcases hr with hD | hL | hP'
  · exact run_shadow_excluded _ _ _ _ _ _ hc.1.1 hd hD
  · exact run_shadow_excluded _ _ _ _ _ _ hc.1.2 hl hL
  · exact run_shadow_excluded _ _ _ _ _ _ hc.2 hP hP'

theorem root32_no_highstop_first_root (E u : Nat)
    (hE : E=201+3360*(6657+8192*32))
    (hroot : 18018+211*u+22155*32=20*2^(E-13)) :
    ¬RunReach (1048576*u+70538) 3 := by
  exact root32_no_highstop_shadow 32 E u 100 256 (by decide) hE hroot (by omega)
    BB6.Agent19Shadow.first_root_shadow_checked

#print axioms run_shadow_excluded
#print axioms root32_no_highstop_shadow
#print axioms root32_no_highstop_first_root


/-- The blank seed has right coordinate one, so large right size alone
    guarantees a source parent, with no restriction on the left coordinate. -/
theorem run_parent_of_right_ge8 (x y : Nat) (hy : 8≤y) (hr : RunReach x y) :
    ∃ a k, RunReach a k ∧ secNext (a,k)=some (x,y) := by
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at ht
    | some p =>
      rcases p with ⟨a,k⟩
      refine ⟨a,k,⟨n,hp⟩,?_⟩
      simpa [BB6.Agent8Section.run,hp] using ht

theorem run_mod_excluded (f p u v q x y : Nat)
    (hc : BB6.Agent19Shadow.modExcluded f p u v=true)
    (hl : BB6.Agent19Shadow.lift p u v x y)
    (hq : p+4≤q) (hs : BB6.Agent19Shadow.RightLarge q y) : ¬RunReach x y := by
  apply BB6.Agent19Shadow.modExcluded_sound RunReach ?_ ?_ f p u v q x y hc hl hq hs
  · intro x y hy ho hs hr
    rcases hr with ⟨n,hn⟩
    cases n with
    | zero => simp [BB6.Agent8Section.run] at hn; omega
    | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n x y hn hy ho
      omega
  · intro x y w hy hv hq hr
    obtain ⟨a,k,hp,hedge⟩ := run_parent_of_right_ge8 x y hy hr
    have hi := (complete_section_inverse a k x y (by omega)).mp hedge
    rcases parent_equations a k x y w hy hv hq hi with hd | ⟨n,hn⟩
    · exact Or.inl ⟨a,k,hp,hd⟩
    · exact Or.inr ⟨a,k,n,hp,hn⟩

/-- All three residuals excluded for an entire root-index cylinder, using
    only the cylinder precision plus the corresponding slope valuations. -/
theorem root32_no_highstop_mod_cylinder (r E u f m j0 : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hroot : 18018+211*u+22155*r=20*2^(E-13))
    (hj : j0≤r/64) (hcon : 2^m∣r/64-j0)
    (hp : m+18≤E-17)
    (hc : BB6.Agent19Shadow.threeCylinderExcluded f m j0=true) :
    ¬RunReach (1048576*u+70538) 3 := by
  intro hT
  obtain ⟨t,hu,hr⟩ := BB6.Agent3Root32HighStopP7.root32_highstop_reduces_to_three_residuals
    r E u hr64 hE hroot hT
  let j := r/64
  have hrj : r=32+64*j := by
    have he := Nat.mod_add_div r 64
    rw [hr64] at he
    exact he.symm
  have heq := BB6.Agent3Root32HighStopIndexMap.root32_original_to_tj u r t j E (by omega) hu hrj hroot
  obtain ⟨hd,hl,hp'⟩ := BB6.Agent19Shadow.three_cylinder_lift t j0 j (E-17) m hj hcon (by omega) heq
  have hlin : BB6.Agent19Shadow.C*j+17300≤E-17+1 := by
    simp only [BB6.Agent19Shadow.C]
    omega
  obtain ⟨sd,sl,sp⟩ := BB6.Agent19Shadow.three_root_large t j (E-17) (by omega) hlin heq
  simp only [BB6.Agent19Shadow.threeCylinderExcluded,Bool.and_eq_true] at hc
  rcases hr with hD | hL | hP
  · exact run_mod_excluded _ _ _ _ _ _ _ hc.1.1 hd (by omega) sd hD
  · exact run_mod_excluded _ _ _ _ _ _ _ hc.1.2 hl (by omega) sl hL
  · exact run_mod_excluded _ _ _ _ _ _ _ hc.2 hp' (by omega) sp hP

theorem mod_cylinder_examples :
    BB6.Agent19Shadow.threeCylinderExcluded 19 5 22=true ∧
    BB6.Agent19Shadow.threeCylinderExcluded 20 6 31=true := by decide

/-- General low/high stop exclusion. No bound j≤3m+1 is needed. -/
theorem run_stop_mod_excluded (f p j m k : Nat) (hp : p+4≤2*m+2)
    (hc : BB6.Agent19StopMod.stopExcluded f p j m=true)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) : ¬RunReach (2*j+1) k :=
  run_mod_excluded f p _ _ (2*m+2) _ _ hc
    (BB6.Agent19StopMod.stop_lift p j m k (by omega) hstop) hp
    (BB6.Agent19StopMod.stop_rightLarge j m k hstop)

/-- Even precision above the stopping exponent is available when j is large. -/
theorem run_stop_general_excluded (f p q j m k : Nat)
    (hp : p+4≤2*m+1+q) (hq : 2^q≤j+2)
    (hc : BB6.Agent19StopMod.generalExcluded f p j m=true)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) : ¬RunReach (2*j+1) k :=
  run_mod_excluded f p _ _ (2*m+1+q) _ _ hc
    (BB6.Agent19StopMod.general_lift p j m k hstop) hp
    (BB6.Agent19StopMod.stop_rightLarge_product j m k q hq hstop)

#print axioms run_parent_of_right_ge8
#print axioms run_mod_excluded
#print axioms root32_no_highstop_mod_cylinder
#print axioms mod_cylinder_examples
#print axioms run_stop_mod_excluded
#print axioms run_stop_general_excluded

end BB6.Agent19Root32Cone
