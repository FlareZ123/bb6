import DrainImageGates
import Agent49InverseWindowSource

namespace BB6.Agent41DrainImageSource
open BB6.Agent41DrainImageDecoder
open BB6.Agent49InverseWindowSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem excessLaws : ExcessLaws BB6.Agent49CorrectionGrowth.excess where
  zero := BB6.Agent49CorrectionGrowth.excess_zero
  r0 := BB6.Agent49CorrectionGrowth.excess_three
  r1 := by
    intro q
    rw [BB6.Agent49CorrectionGrowth.excess_one]
    omega
  r2 := by
    intro q
    rw [BB6.Agent49CorrectionGrowth.excess_two]
    omega

theorem image_decoder (b : Nat) :
    inverse (BB6.Agent49CorrectionGrowth.image b)=some b := by
  exact inverse_complete excessLaws b

/-- Every successful original drain in the large-first sector decodes exactly. -/
def Decoded (A b z x y : Nat) : Prop :=
  2*inverseBudget y≤x →
  x≤A+inverseBudget y ∧
  y=z+BB6.Agent49CorrectionGrowth.image b ∧ inverse (y-z)=some b

theorem source_decoded (A b z x y : Nat)
    (h : drainB A b z=some (.D x y)) : Decoded A b z x y := by
  intro hx
  have hw := source_drain_window A b z x y h
  unfold Window at hw
  have hi := source_large_first_image A b z x y h hx
  have hd : y-z=BB6.Agent49CorrectionGrowth.image b := by omega
  exact ⟨hw.2.1,hi,by rw [hd]; exact image_decoder b⟩

/-- All source branches with large first output and y>14 must pass
one of the two parity-compatible image gates. -/
theorem no_parent_of_blocked (a d x y : Nat) (hy : 14<y)
    (hx : 2*inverseBudget y≤x) (hb : blocked y) :
    highLevelNext (.D a d) ≠ some (.D x y) := by
  intro h
  have hp := parent_envelope_complete Decoded source_decoded a d x y h
  have hn : 0 < inverseBudget y := by unfold inverseBudget; omega
  unfold ParentEnvelope at hp
  rcases hp with haxis|hlo|hle|hdiag|hro|hre
  · rcases haxis with ⟨_,haxis|haxis⟩ <;> omega
  · obtain ⟨A,b,hd,_,_,hdb,hdec⟩ := hlo
    obtain ⟨_,hi,hg⟩ := hdec hx
    have hpar := image_parity excessLaws b
    change BB6.Agent49CorrectionGrowth.image b%2=b%2 at hpar
    have hy' : y%2≠0 := by omega
    unfold blocked at hb
    rw [if_neg hy'] at hb
    rw [hb.1] at hg
    contradiction
  · obtain ⟨A,b,hd,_,_,hdb,hdec⟩ := hle
    obtain ⟨_,hi,hg⟩ := hdec hx
    have hpar := image_parity excessLaws b
    change BB6.Agent49CorrectionGrowth.image b%2=b%2 at hpar
    have hy' : y%2=0 := by omega
    unfold blocked at hb
    rw [if_pos hy'] at hb
    rw [hb.1] at hg
    contradiction
  · obtain ⟨_,_,hdec⟩ := hdiag
    have hw := (hdec hx).1
    omega
  · obtain ⟨A,b,ha,hd,hab,_,hdec⟩ := hro
    obtain ⟨_,hi,hg⟩ := hdec hx
    have hpar := image_parity excessLaws b
    change BB6.Agent49CorrectionGrowth.image b%2=b%2 at hpar
    have hy' : y%2=0 := by omega
    unfold blocked at hb
    rw [if_pos hy'] at hb
    rw [hb.2] at hg
    contradiction
  · obtain ⟨A,b,ha,hd,hab,_,hdec⟩ := hre
    obtain ⟨_,hi,hg⟩ := hdec hx
    have hpar := image_parity excessLaws b
    change BB6.Agent49CorrectionGrowth.image b%2=b%2 at hpar
    have hy' : y%2≠0 := by omega
    unfold blocked at hb
    rw [if_neg hy'] at hb
    simp only [Nat.sub_zero] at hg
    rw [hb.2] at hg
    contradiction

/-- Authentic all-time orbit exclusion, without any finite-run hypothesis. -/
theorem root_excluded_of_blocked (n x y : Nat) (hy : 14<y)
    (hx : 2*inverseBudget y≤x) (hb : blocked y) :
    BB6.Agent49ParitySource.run n ≠ some (.D x y) := by
  intro h
  cases n with
  | zero =>
    simp only [BB6.Agent49ParitySource.run] at h
    injection h with h
    cases h
    omega
  | succ n =>
    simp only [BB6.Agent49ParitySource.run] at h
    cases hr : BB6.Agent49ParitySource.run n with
    | none => rw [hr] at h; contradiction
    | some s =>
      rw [hr] at h
      cases s with
      | D a d => exact no_parent_of_blocked a d x y hy hx hb h

/-- In every band, each triple contains a complete vertical ray excluded
from every step of the authentic orbit. -/
theorem band_root_exclusion (k j : Nat) (hk : 2≤k)
    (hj : 1≤j) (hj' : j≤k+3) :
    let y := 9*tau k+2*j+(if k%2=0 then 2 else 0)
    ∃ r, r≤2 ∧ ∀ n x, 2*inverseBudget (y+2*r)≤x →
      BB6.Agent49ParitySource.run n ≠ some (.D x (y+2*r)) := by
  dsimp
  let y := 9*tau k+2*j+(if k%2=0 then 2 else 0)
  have hτ := tau_mono hk
  have hτ' : tau 2=4 := by decide
  rw [hτ'] at hτ
  have hy : 14<y := by dsimp [y]; omega
  have hb : blocked y ∨ blocked (y+2) ∨ blocked (y+4) :=
    blocked_band excessLaws k j hk hj hj'
  rcases hb with h|h|h
  · refine ⟨0,by decide,?_⟩
    intro n x hx
    exact root_excluded_of_blocked n x y hy hx h
  · refine ⟨1,by decide,?_⟩
    intro n x hx
    exact root_excluded_of_blocked n x (y+2) (by omega) hx h
  · refine ⟨2,by decide,?_⟩
    intro n x hx
    exact root_excluded_of_blocked n x (y+4) (by omega) hx h

#print axioms image_decoder
#print axioms source_decoded
#print axioms no_parent_of_blocked
#print axioms root_excluded_of_blocked
#print axioms band_root_exclusion
end BB6.Agent41DrainImageSource
