import DirectBlocks
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 200000

namespace BB6.Agent12BranchingBlocks
open BB6.Agent42DirectBlocks

/-- The necessary inverse equations already certified for Machine C.
    The adapter uses Agent 42's source_parent, including x=1. -/
abbrev ParentLaw (reach : Nat → Nat → Prop) : Prop :=
  ∀ x y v, reach x y → 8≤y → (x+y+(x+y)%2)%2^(v+1)=2^v →
    2^v<x+y+(x+y)%2 → ∃ a z, reach a z ∧
      ((y%2=0 ∧ a+2=x+y ∧ 2*z+2=y) ∨
      ∃ n, n+2≤v ∧ n%2=(x+1+(x+y)%2)%2 ∧
        x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2) ∧
        2*z+a+7+3*n=x+2*y)

/-- At the sum-seven (odd left) or sum-zero (even left) terminal,
    valuation three and the depth parity leave exactly the direct and
    depth-one alternatives. Each possible parent is an odd forbidden image. -/
theorem branching_terminal_excluded (reach : Nat → Nat → Prop)
    (parent : ParentLaw reach) (forbid : ForbiddenLaw reach)
    (x y H : Nat) (hH : 7≤H) (hy : y+2=2*H)
    (hpar : (x%4=3 ∧ H%4=3) ∨ (x%4=0 ∧ H%4=1))
    (hQ : (x+y+(x+y)%2)%32=24) : ¬reach x y := by
  intro hr
  have hv : (x+y+(x+y)%2)%2^(3+1)=2^3 := by
    change (x+y+(x+y)%2)%16=8
    omega
  obtain ⟨a,z,hp,he⟩ := parent x y 3 hr (by omega) hv (by omega)
  rcases hpar with ⟨hx,hH4⟩ | ⟨hx,hH4⟩ <;>
    rcases he with ⟨_,ha,hz⟩ | ⟨n,hn,hnp,ha,hz⟩
  · exact forbid a z (by omega) (by omega) (Or.inr (by omega)) hp
  · have hn1 : n=1 := by omega
    subst n
    change x+y+(x+y)%2=4*(a+2+(x+y)%2) at ha
    have ha8 : a%8=3 := by omega
    exact forbid a z (by omega) (by omega) (Or.inr (by omega)) hp
  · exact forbid a z (by omega) (by omega) (Or.inl (by omega)) hp
  · have hn1 : n=1 := by omega
    subst n
    change x+y+(x+y)%2=4*(a+2+(x+y)%2) at ha
    have ha8 : a%8=4 := by omega
    exact forbid a z (by omega) (by omega) (Or.inl (by omega)) hp

/-- Reuse the existing unbounded forced-block theorem; the new work is
    the terminal two-parent fan, not another direct-only induction. -/
theorem branching_ladder_excluded (reach : Nat → Nat → Prop)
    (direct : DirectLaw reach) (parent : ParentLaw reach) (forbid : ForbiddenLaw reach)
    (t H x y : Nat) (hH : 7≤H)
    (hpar : (x%4=3 ∧ H%4=3) ∨ (x%4=0 ∧ H%4=1))
    (hy : y+2=2^(t+1)*H)
    (hphase : (x+2*y+28*t+2+x%2)%32=(2*H+24)%32) : ¬reach x y := by
  have hy' : y+2=2^t*(2*H) := by rw [hy,Nat.pow_succ,Nat.mul_assoc]
  have hx4 : x%4=0 ∨ x%4=3 := by omega
  obtain ⟨a,ha,hm,ha4⟩ := direct_block reach direct t x y (2*H)
    (by omega) (by omega) hy' hx4
  let k := 2*H-2
  have hk : k+2=2*H := by dsimp [k]; omega
  have hm' : a+2*k+4*t=x+2*y := hm
  have hp : (a%4=3 ∧ H%4=3) ∨ (a%4=0 ∧ H%4=1) := by omega
  have hodd : (a+k)%2=x%2 := by omega
  have hQ : (a+k+(a+k)%2)%32=24 := by
    rw [hodd]
    omega
  intro hr
  exact branching_terminal_excluded reach parent forbid a k H hH hk hp hQ (ha.mp hr)

/-- No precision cap: jump the exact direct block, then test the fan. -/
def branchingBlockExcluded (x y : Nat) : Bool :=
  let d := directDepth y
  let H := directOdd y
  decide (1≤d ∧ y+2=2^d*H ∧ 7≤H ∧
    ((x%4=3 ∧ H%4=3) ∨ (x%4=0 ∧ H%4=1)) ∧
    (x+2*y+28*(d-1)+2+x%2)%32=(2*H+24)%32)

theorem branchingBlockExcluded_sound (reach : Nat → Nat → Prop)
    (direct : DirectLaw reach) (parent : ParentLaw reach) (forbid : ForbiddenLaw reach)
    (x y : Nat) (h : branchingBlockExcluded x y=true) : ¬reach x y := by
  simp only [branchingBlockExcluded,decide_eq_true_eq] at h
  obtain ⟨hd,hy,hH,hpar,hphase⟩ := h
  change 1≤directDepth y at hd
  have he : directDepth y-1+1=directDepth y := by omega
  exact branching_ladder_excluded reach direct parent forbid (directDepth y-1)
    (directOdd y) x y hH hpar (by rwa [he]) hphase

/-- A newly accepted block cannot have the earlier direct-only certificate:
    that certificate requires the other terminal sum residue. -/
theorem branching_disjoint_direct (x y : Nat) (h : branchingBlockExcluded x y=true) :
    directBlockExcluded x y=false := by
  simp only [branchingBlockExcluded,decide_eq_true_eq] at h
  obtain ⟨hd,_,_,hpar,hphase⟩ := h
  cases he : directBlockExcluded x y with
  | false => rfl
  | true =>
    simp only [directBlockExcluded,decide_eq_true_eq] at he
    obtain ⟨_,_,_,hH4,hx4,hm⟩ := he
    change 1≤directDepth y at hd
    change ((x%4=3 ∧ directOdd y%4=3) ∨ (x%4=0 ∧ directOdd y%4=1)) at hpar
    change (x+2*y+28*(directDepth y-1)+2+x%2)%32=(2*directOdd y+24)%32 at hphase
    change x%4=3 at hx4
    change directOdd y%4=3 at hH4
    change (x+2*y)%8=(4*directDepth y+3)%8 at hm
    omega

/-- Exact high-stop mass eliminates the exponential from the terminal
    phase test. Only the odd part of y+2 and its valuation are needed. -/
theorem high_branching_excluded (reach : Nat → Nat → Prop)
    (direct : DirectLaw reach) (parent : ParentLaw reach) (forbid : ForbiddenLaw reach)
    (m j k t H : Nat) (hm : 1≤m) (hH : 7≤H) (hH4 : H%4=3)
    (hy : k+2=2^(t+1)*H) (hphase : (H+3*m+2*t+14)%16=0)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : ¬reach (2*j+3) k := by
  let P := 2^(2*m+2)
  have hP : P%16=0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.pow_dvd_pow 2 (by omega : 4≤2*m+2)
  have hp : (P*(j+3))%16=0 := by rw [Nat.mul_mod,hP]; simp
  change k+j+3*m+5=P*(j+3) at hstop
  have hk2 : k%2=0 := by
    rw [Nat.pow_succ,show (2^t*2)*H=2*(2^t*H) by ac_rfl] at hy
    omega
  apply branching_ladder_excluded reach direct parent forbid t H (2*j+3) k hH
    (Or.inl ⟨by omega,hH4⟩) hy
  omega

private theorem pow_bound (m : Nat) (hm : 1≤m) : 8*m+8≤(2:Nat)^(2*m+2) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hz : m=0
    · subst m; decide
    · have h := ih (by omega)
      rw [show 2*(m+1)+2=2*m+2+2 by omega,Nat.pow_add]
      change 8*(m+1)+8≤2^(2*m+2)*4
      omega

/-- An explicit two-parameter family beyond the direct-only terminal and
    the original 2m+2-bit signed-cone budget. -/
theorem high_branching_family (reach : Nat → Nat → Prop)
    (direct : DirectLaw reach) (parent : ParentLaw reach) (forbid : ForbiddenLaw reach)
    (m q j k : Nat) (hm : 5≤m) (hm4 : m%4=1) (hq : 1≤q)
    (hq32 : q%32=(11*m+4)%32)
    (hj : j+3*m+3=q*2^(2*m+2))
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : ¬reach (2*j+3) k := by
  let P := 2^(2*m+2)
  have hP : 8*m+8≤P := pow_bound m (by omega)
  have hP32 : P%32=0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.pow_dvd_pow 2 (by omega : 5≤2*m+2)
  have hqP32 : (q*P)%32=0 := by rw [Nat.mul_mod,hP32]; simp
  change j+3*m+3=q*P at hj
  have hqp : q*(3*m+15)≤q*P := Nat.mul_le_mul_left q (by omega)
  have hqmul : q*(3*m+15)=q*(3*m+14)+q := by
    rw [show 3*m+15=3*m+14+1 by omega,Nat.mul_add,Nat.one_mul]
  have hbase : 3*m+14≤q*(3*m+14) := by
    simpa using Nat.mul_le_mul_right (3*m+14) hq
  have hq_bound : q+14≤j+3 := by omega
  let L := j+3-q
  have hL : L+q=j+3 := by dsimp [L]; omega
  have hL8 : L%8=6 := by omega
  have hLbound : 14≤L := by omega
  let H := L/2
  have hHL : L=2*H := by dsimp [H]; omega
  have hH7 : 7≤H := by omega
  have hH4 : H%4=3 := by omega
  change k+j+3*m+5=P*(j+3) at hstop
  have hk : k+2=P*L := by
    have hh : P*(j+3)=P*L+P*q := by rw [←hL,Nat.mul_add]
    rw [Nat.mul_comm P q] at hh
    omega
  apply high_branching_excluded reach direct parent forbid m j k (2*m+2) H
    (by omega) hH7 hH4 ?_ (by omega) hstop
  rw [Nat.pow_succ,show (2^(2*m+2)*2)*H=P*(2*H) by simp [P,Nat.mul_assoc],←hHL]
  exact hk

#print axioms branching_terminal_excluded
#print axioms branching_ladder_excluded
#print axioms branchingBlockExcluded_sound
#print axioms branching_disjoint_direct
#print axioms high_branching_excluded
#print axioms high_branching_family
end BB6.Agent12BranchingBlocks
