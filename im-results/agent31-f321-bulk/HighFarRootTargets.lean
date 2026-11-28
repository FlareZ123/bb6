import HighFarTerminalFamily
import Phase6Bridge
import Lean.Elab.Tactic.Omega

/-!
Root-facing reduction for the infinite H^(24k+22)/Far terminal-suffix family.

Every member of this family is a genuine source-faithful terminal suffix and
passes the coarse terminal/anchor residue filters.  This file proves that if
its c=1 anchor ever occurs on the authentic root orbit, the producing anchor
move is necessarily MiddleOdd.  Equal is eliminated uniformly by the Phase6
root invariant.
-/

namespace BB6.Agent31F321HighFarRootTargets
open BB6.Agent31F321Density
open BB6.Agent31F321HighFarFamily
open BB6.Agent2F321Phase6
open BB6.Agent2F321Phase6Bridge

/-- Exact source reset branches whose output second counter is at most two. -/
def SmallAnchorMove (a d R c : Nat) : Prop :=
  (a=d ∧ R=2*a+4 ∧ c=1) ∨
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=0 ∧ R=4*a+6 ∧ c=2) ∨
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=1 ∧ R=4*a+6 ∧ c=1)

theorem smallAnchorMove_source {a d R c : Nat}
    (h : SmallAnchorMove a d R c) : CounterMove a d R c := by
  unfold SmallAnchorMove at h
  rcases h with hE | hM
  · rcases hE with ⟨rfl,rfl,rfl⟩
    exact CounterMove.equal a
  · rcases hM with hEven | hOdd
    · rcases hEven with ⟨h1,h2,hp,rfl,rfl⟩
      exact CounterMove.middleEven d h1 h2 hp
    · rcases hOdd with ⟨h1,h2,hp,rfl,rfl⟩
      exact CounterMove.middleOdd d h1 h2 hp

def dangerM (k : Nat) : Nat := 8*k+6
def dangerN (k : Nat) : Nat := 24*k+22
def dangerT (k : Nat) : Nat := highFarT (dangerM k)
def dangerR (k : Nat) : Nat := 2*dangerT k-(dangerN k+6)

/-- Restatement of the infinite source-faithful family in named coordinates. -/
theorem danger_family (k : Nat) :
    CounterReach (dangerR k) 1 (dangerN k+1)
        (dangerT k+1) (dangerT k) ∧
      dangerT k % 384 = 37 ∧ dangerR k % 24 = 22 := by
  simpa [dangerM,dangerN,dangerT,dangerR]
    using high_far_root_residue_subfamily k

/-- No dangerous-family anchor can be produced by Equal on the root orbit.
    R == 22 mod 24 would force the equal predecessor a == 9 mod 12, contrary
    to the all-depth Phase6 invariant for reachable diagonal states. -/
theorem danger_equal_predecessor_unreachable
    {k n a : Nat}
    (hr : CounterReach 1 1 n a a)
    (hR : 2*a+4 = dangerR k) :
    False := by
  have hRm : dangerR k % 24 = 22 := (danger_family k).2.2
  have ha12 : a % 12 = 9 := by omega
  have hp := counterReach_phase6 hr
  rcases hp with hseed | hp
  · omega
  · unfold Phase6 at hp
    rcases hp with h01 | h02 | h15 <;> omega

/-- Uniform root reduction: if a member of the dangerous H^(24k+22)/Far
    family has its c=1 anchor on the authentic root orbit, that anchor was
    produced by a MiddleOdd reset. -/
theorem danger_anchor_requires_middleOdd
    {k n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : SmallAnchorMove a d (dangerR k) 1) :
    a<d ∧ d<3*a+1 ∧ (d-a)%2=1 ∧ 4*a+6=dangerR k := by
  unfold SmallAnchorMove at ha
  rcases ha with hE | hM
  · rcases hE with ⟨had,hR,hc⟩
    have hrEq : CounterReach 1 1 n a a := by simpa [had] using hr
    exact False.elim (danger_equal_predecessor_unreachable hrEq hR.symm)
  · rcases hM with hEven | hOdd
    · rcases hEven with ⟨h1,h2,hp,hR,hc⟩
      omega
    · rcases hOdd with ⟨h1,h2,hp,hR,hc⟩
      exact ⟨h1,h2,hp,hR.symm⟩

#print axioms smallAnchorMove_source
#print axioms danger_family
#print axioms danger_equal_predecessor_unreachable
#print axioms danger_anchor_requires_middleOdd
end BB6.Agent31F321HighFarRootTargets
