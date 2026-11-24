import Agent41RootMassGapSource
import Agent41V3MinCounterexampleSource

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Exact ell=20 root exclusion for the cone-only synchronization family

The all-depth cone-only family in Agent 1's
`InfiniteConeSyncNonclosure.md` specializes at ell=20 to
`q = 3^8 * (1 + 3^8 * (3 + 4*r)) / 2` and source state
`D(4*q+400,q)`.  Its mass-depth condition is exactly
`3^19 < 2*(5*q+400)+7 <= 3^20`.

The arithmetic below proves that this slice has only r=1,2,3.
Agent 41's unchanged-source certificates then identify each exact
transition and exclude both endpoints from the authentic blank-root orbit
using adjacent root-mass gaps.  This closes the entire ell=20 slice, not the
all-depth family or Machine #623.
-/

namespace BB6.Agent27ConeOnlyEll20

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent41RootHistory
open BB6.Agent41V3MinCounterexample

/-- The ell=20 progression identity obtained from k=7, j=19, n=8, t0=3. -/
theorem ell20_q_progression_identity (r : Nat) :
    3^8 * (1 + 3^8 * (3 + 4*r)) =
      2 * (64573362 + 86093442*r) := by
  norm_num
  ring

/-- The mass-depth condition ell_S=20 for S=5*q+400 is this exact interval. -/
theorem ell20_family_q_bounds (q : Nat)
    (hdepth :
      3^19 < 2*(5*q+400)+7 ∧
      2*(5*q+400)+7 ≤ 3^20) :
    116226067 ≤ q ∧ q ≤ 348678359 := by
  norm_num at hdepth
  omega

/-- Only the three parameters r=1,2,3 in the progression lie at mass depth 20. -/
theorem ell20_family_parameter (r q : Nat)
    (hq : 2*q = 3^8 * (1 + 3^8 * (3 + 4*r)))
    (hdepth :
      3^19 < 2*(5*q+400)+7 ∧
      2*(5*q+400)+7 ≤ 3^20) :
    r = 1 ∨ r = 2 ∨ r = 3 := by
  have hq' : q = 64573362 + 86093442*r := by
    have hid := ell20_q_progression_identity r
    omega
  have hb := ell20_family_q_bounds q hdepth
  omega

/-- Every ell=20 member has one of the three exact original-source transitions. -/
theorem ell20_family_exact_step (r q : Nat)
    (hq : 2*q = 3^8 * (1 + 3^8 * (3 + 4*r)))
    (hdepth :
      3^19 < 2*(5*q+400)+7 ∧
      2*(5*q+400)+7 ≤ 3^20) :
    (r = 1 ∧
      highLevelNext (.D (4*q+400) q) = some (.D 452000798 452000456)) ∨
    (r = 2 ∧
      highLevelNext (.D (4*q+400) q) = some (.D 710281126 710280778)) ∨
    (r = 3 ∧
      highLevelNext (.D (4*q+400) q) = some (.D 968561452 968561102)) := by
  rcases ell20_family_parameter r q hq hdepth with hr | hr | hr
  · subst r
    have hqv : q = 150666804 := by omega
    subst q
    exact Or.inl ⟨rfl, by simpa using cone_only_ell20_r1_step⟩
  · subst r
    have hqv : q = 236760246 := by omega
    subst q
    exact Or.inr (Or.inl ⟨rfl, by simpa using cone_only_ell20_r2_step⟩)
  · subst r
    have hqv : q = 322853688 := by omega
    subst q
    exact Or.inr (Or.inr ⟨rfl, by simpa using cone_only_ell20_r3_step⟩)

/-- Each ell=20 family edge has both endpoints outside the authentic blank-root orbit. -/
theorem ell20_family_edge_endpoints_not_root
    (r q n : Nat)
    (hq : 2*q = 3^8 * (1 + 3^8 * (3 + 4*r)))
    (hdepth :
      3^19 < 2*(5*q+400)+7 ∧
      2*(5*q+400)+7 ≤ 3^20) :
    (r = 1 ∧
      highLevelNext (.D (4*q+400) q) = some (.D 452000798 452000456) ∧
      run n ≠ some (.D (4*q+400) q) ∧
      run n ≠ some (.D 452000798 452000456)) ∨
    (r = 2 ∧
      highLevelNext (.D (4*q+400) q) = some (.D 710281126 710280778) ∧
      run n ≠ some (.D (4*q+400) q) ∧
      run n ≠ some (.D 710281126 710280778)) ∨
    (r = 3 ∧
      highLevelNext (.D (4*q+400) q) = some (.D 968561452 968561102) ∧
      run n ≠ some (.D (4*q+400) q) ∧
      run n ≠ some (.D 968561452 968561102)) := by
  rcases ell20_family_parameter r q hq hdepth with hr | hr | hr
  · subst r
    have hqv : q = 150666804 := by omega
    subst q
    exact Or.inl
      ⟨rfl,
       by simpa using cone_only_ell20_r1_step,
       by simpa using cone_only_ell20_r1_not_root n,
       cone_only_ell20_r1_target_not_root n⟩
  · subst r
    have hqv : q = 236760246 := by omega
    subst q
    exact Or.inr (Or.inl
      ⟨rfl,
       by simpa using cone_only_ell20_r2_step,
       by simpa using cone_only_ell20_r2_not_root n,
       cone_only_ell20_r2_target_not_root n⟩)
  · subst r
    have hqv : q = 322853688 := by omega
    subst q
    exact Or.inr (Or.inr
      ⟨rfl,
       by simpa using cone_only_ell20_r3_step,
       by simpa using cone_only_ell20_r3_not_root n,
       cone_only_ell20_r3_target_not_root n⟩)

#print axioms ell20_q_progression_identity
#print axioms ell20_family_q_bounds
#print axioms ell20_family_parameter
#print axioms ell20_family_exact_step
#print axioms ell20_family_edge_endpoints_not_root

end BB6.Agent27ConeOnlyEll20
