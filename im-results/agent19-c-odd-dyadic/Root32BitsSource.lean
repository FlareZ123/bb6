import ShadowBitsLift
import ShadowBitsExec
import ShadowScalar
import DyadicReach
import Root32ConeClosure

namespace BB6.Agent19Root32Bits

open BB6.Agent3Root32HighStopIntegrated (RunReach)
open BB6.Agent19ShadowBits
open BB6.Agent46

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private theorem run_parent_law : BB6.Agent21Dyadic.ParentLaw RunReach := by
  intro x y v hr hy hmod hgt
  obtain ⟨a,k,hreach,hedge⟩ := BB6.Agent19Root32Cone.run_parent_of_right_ge8 x y hy hr
  have hi := (complete_section_inverse a k x y (by omega)).mp hedge
  exact ⟨a,k,hreach,parent_equations a k x y v hy hmod hgt hi⟩

private theorem unscale_lift (p a u : Nat) (h : 2^p∣22155*a+105*u) :
    2^p∣211*a+u := by
  have h' : 2^p∣105*(211*a+u) := by
    rw [Nat.mul_add,←Nat.mul_assoc]
    exact h
  exact (Nat.Coprime.pow_left p (by decide : Nat.Coprime 2 105)).dvd_of_dvd_mul_left h'

private theorem large_of_right (n q y : Nat)
    (h : BB6.Agent19Shadow.RightLarge q y) (hn : n+4≤q) :
    BB6.Agent21Dyadic.Large (n+2) y := by
  have h2 : 2^(n+4)≤2^q := Nat.pow_le_pow_right (by decide) hn
  rw [show n+4=(n+2)+2 by omega,Nat.pow_add] at h2
  change 2^(n+2)*4≤2^q at h2
  change 3*2^(n+2)≤y+2
  unfold BB6.Agent19Shadow.RightLarge at h
  omega

/-- Source reachability forces an actual nonempty compact bit frontier;
    no recursive valuation guard or source-coordinate materialization. -/
theorem run_bits_excluded (m x n q a b : Nat)
    (g : BB6.Agent19Scalar.Good m x)
    (hl : BB6.Agent19Shadow.lift (n+1)
      (105*BB6.Agent19Scalar.U m x) (105*BB6.Agent19Scalar.V m x) a b)
    (hs : BB6.Agent19Shadow.RightLarge q b) (hn : n+4≤q)
    (hc : check m x n=true) : ¬RunReach a b := by
  intro hr
  have ho := BB6.Agent21Dyadic.reach_open RunReach run_parent_law n a b
    (large_of_right n q b hs hn) hr
  change SignedOpen (sourceS a b) (sourceZ a b) n at ho
  have hm : BB6.Agent19Scalar.U m x+2*BB6.Agent19Scalar.V m x=5+211*m := by
    simp only [BB6.Agent19Scalar.Good,BB6.Agent19Scalar.U,BB6.Agent19Scalar.V,
      BB6.Agent19Scalar.base,BB6.Agent19Scalar.s] at g ⊢
    omega
  have ha := unscale_lift (n+1) a (BB6.Agent19Scalar.U m x) hl.1
  have hb := unscale_lift (n+1) b (BB6.Agent19Scalar.V m x) hl.2
  obtain ⟨v,hv⟩ := source_frontier_nonempty m x _ _ a b n hm rfl ha hb ho
  rw [(check_iff m x n).mp hc] at hv
  simp at hv

private theorem rays_good (j : Nat) :
    BB6.Agent19Scalar.Good (BB6.Agent19Scalar.dRay.m j) (BB6.Agent19Scalar.dRay.x j) ∧
    BB6.Agent19Scalar.Good (BB6.Agent19Scalar.lRay.m j) (BB6.Agent19Scalar.lRay.x j) ∧
    BB6.Agent19Scalar.Good (BB6.Agent19Scalar.pRay.m j) (BB6.Agent19Scalar.pRay.x j) := by
  simp only [BB6.Agent19Scalar.Good,BB6.Agent19Scalar.base,BB6.Agent19Scalar.s,
    BB6.Agent19Scalar.Ray.m,BB6.Agent19Scalar.Ray.x,
    BB6.Agent19Scalar.dRay,BB6.Agent19Scalar.lRay,BB6.Agent19Scalar.pRay]
  omega

def threeBitsExcluded (n j : Nat) : Bool :=
  check (BB6.Agent19Scalar.dRay.m j) (BB6.Agent19Scalar.dRay.x j) n &&
  check (BB6.Agent19Scalar.lRay.m j) (BB6.Agent19Scalar.lRay.x j) n &&
  check (BB6.Agent19Scalar.pRay.m j) (BB6.Agent19Scalar.pRay.x j) n

/-- Full exact original root32 high-stop exclusion. The cutoff n counts
    binary cost, and the checker stops immediately on the empty frontier. -/
theorem root32_no_highstop_bits (r E u n : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hroot : 18018+211*u+22155*r=20*2^(E-13))
    (hn : n+4≤E-17)
    (hc : threeBitsExcluded n (r/64)=true) :
    ¬RunReach (1048576*u+70538) 3 := by
  intro hT
  obtain ⟨t,hu,hr⟩ := BB6.Agent3Root32HighStopP7.root32_highstop_reduces_to_three_residuals
    r E u hr64 hE hroot hT
  let j := r/64
  have hrj : r=32+64*j := by
    have he := Nat.mod_add_div r 64
    rw [hr64] at he
    exact he.symm
  have heq := BB6.Agent3Root32HighStopIndexMap.root32_original_to_tj u r t j E
    (by omega) hu hrj hroot
  obtain ⟨hd,hl,hp⟩ := BB6.Agent19Shadow.three_shadow_lift t j (E-17) (n+1) (by omega) heq
  have hlin : BB6.Agent19Shadow.C*j+17300≤E-17+1 := by
    simp only [BB6.Agent19Shadow.C]
    omega
  obtain ⟨sd,sl,sp⟩ := BB6.Agent19Shadow.three_root_large t j (E-17) (by omega) hlin heq
  obtain ⟨du,dv,lu,lv,pu,pv⟩ := BB6.Agent19Scalar.source_ray_coordinates j
  change 105*BB6.Agent19Scalar.U _ _=BB6.Agent19Shadow.rootShadow _ _ j at du lu pu
  change 105*BB6.Agent19Scalar.V _ _=BB6.Agent19Shadow.rootShadow _ _ j at dv lv pv
  obtain ⟨gd,gl,gp⟩ := rays_good j
  simp only [threeBitsExcluded,Bool.and_eq_true] at hc
  rcases hr with hD | hL | hP
  · exact run_bits_excluded _ _ n (E-17) _ _ gd (by rwa [du,dv]) sd hn hc.1.1 hD
  · exact run_bits_excluded _ _ n (E-17) _ _ gl (by rwa [lu,lv]) sl hn hc.1.2 hL
  · exact run_bits_excluded _ _ n (E-17) _ _ gp (by rwa [pu,pv]) sp hn hc.2 hP

#print axioms run_bits_excluded
#print axioms root32_no_highstop_bits

end BB6.Agent19Root32Bits
