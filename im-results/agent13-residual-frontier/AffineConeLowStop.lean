import AffineConeKernel
import EvenOddLowStopEvenUnique
import One307Source
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000
namespace BB6.Agent13AffineCone
open BB6.Agent46

/-- Authentic source specialization, with no copied reach predicate. -/
theorem source_excluded (f : Nat) (r : Ray) (h : excluded f r=true) (t : Nat) :
    ¬BB6.Agent3.CReach (r.x.eval t) (r.y.eval t) := by
  apply excluded_sound BB6.Agent3.CReach ?_ BB6.Agent13TwoParent.odd_forbidden_image f r h t
  intro x y hx hy hr
  obtain ⟨a,k,hp,hedge⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  exact ⟨a,k,hp,(complete_section_inverse a k x y (by omega)).mp hedge⟩

def payloadBase (z : Nat) : Nat := 2^64+(16384-(6*z+1)%16384)%16384
def lowRay (z : Nat) : Ray :=
  ⟨⟨173*16384,173*payloadBase z+24⟩,⟨339*8192,(339*payloadBase z+47)/2⟩⟩
def lowExcluded (f z : Nat) : Bool := z%2==0 && excluded f (lowRay z)

private theorem succ_le_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem payload_representation (z u : Nat) (hu : u+6*z+1=2^(1024*z+129)) :
    ∃ t : Nat, u=16384*t+payloadBase z := by
  have hd : (2:Nat)^14 ∣ 2^(1024*z+129) := Nat.pow_dvd_pow 2 (by omega)
  have hm : (2^(1024*z+129))%16384=0 := Nat.mod_eq_zero_of_dvd hd
  have hp : 2^(1024*z+129)=2^65*2^(1024*z+64) := by
    rw [show 1024*z+129=65+(1024*z+64) by omega,Nat.pow_add]
  have hbound := succ_le_pow (1024*z+64)
  have hl : 2^64+16384≤u := by rw [hp] at hu; omega
  have hr : u%16384=payloadBase z%16384 := by
    unfold payloadBase
    omega
  have hbase : payloadBase z≤u := by unfold payloadBase; omega
  refine ⟨(u-payloadBase z)/16384,?_⟩
  omega

theorem lowRay_eval (z u t : Nat) (hu : u=16384*t+payloadBase z) :
    (lowRay z).x.eval t=173*u+24 ∧ (lowRay z).y.eval t=(339*u+47)/2 := by
  rw [hu]
  simp only [lowRay,Linear.eval,Nat.mul_add,Nat.mul_assoc]
  omega

theorem stopping_payload (z m k : Nat) (hm : m=512*z+67) (hstop : k+3*m+4=2^(2*m+3)) :
    ∃ u, k=256*u+51 ∧ u+6*z+1=2^(1024*z+129) := by
  have hp : 2^(2*m+3)=256*2^(1024*z+129) := by
    rw [show 2*m+3=(1024*z+129)+8 by omega,Nat.pow_add]
    change 2^(1024*z+129)*256=256*2^(1024*z+129)
    exact Nat.mul_comm _ _
  rw [hp] at hstop
  refine ⟨k/256,?_,?_⟩ <;> omega

/-- Complete original-machine low-stop exclusion on every accepted
    affine family, without bounding the genuine blank run. -/
theorem low_stop_affine_excluded (f z m k : Nat)
    (hm : m=512*z+67) (hstop : k+3*m+4=2^(2*m+3))
    (h : lowExcluded f z=true) : ¬BB6.Agent3.CReach 1 k := by
  obtain ⟨u,hk,hu⟩ := stopping_payload z m k hm hstop
  obtain ⟨t,ht⟩ := payload_representation z u hu
  obtain ⟨hx,hy⟩ := lowRay_eval z u t ht
  have hh := h
  simp only [lowExcluded,Bool.and_eq_true,beq_iff_eq] at hh
  intro hr
  rw [hk] at hr
  have hR := BB6.Agent13One307.four_step_to_rectangle u hr
  have hP := BB6.Agent13LowEvenRoot.even_low_ray_reach_forces_unique_parent z u hu hh.1 hR
  exact (source_excluded f (lowRay z) hh.2 t) (by rw [hx,hy]; exact hP)

/-- The checker is a genuinely periodic filter on the unbounded index. -/
theorem lowExcluded_periodic (f z : Nat) : lowExcluded f z=lowExcluded f (z%8192) := by
  have hb : payloadBase z=payloadBase (z%8192) := by unfold payloadBase; omega
  have hpar : z%2=(z%8192)%2 := by omega
  simp only [lowExcluded,lowRay,hb,hpar]

-- Interpreted executable census; soundness theorem does not rely on it.
#eval ((List.range 8192).filter (lowExcluded 20)).length
#print axioms source_excluded
#print axioms low_stop_affine_excluded
#print axioms lowExcluded_periodic
end BB6.Agent13AffineCone
