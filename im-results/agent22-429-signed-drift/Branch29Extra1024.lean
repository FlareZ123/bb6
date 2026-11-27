import BB429InverseKernel
import BB429FiniteAvoidance
import Lean.Elab.Tactic.Omega

/-!
# Eight new complete branch-29 q(mod1024) blank-root exclusions

For r in {15,47,79,191,255,383,447,639}, the true #429 accelerated blank
orbit never reaches (32q+29,64q+55) for ANY q congruent to r mod 1024.

The proof has two components: a single kernel-checked finite blank trace
with strict monotone-rank cutoff for each r<1024, and a uniform original
source affine inverse-tree certificate for all q>=1024. The shift of
the affine parameter by 1024 is crucial: the unshifted standard certificate
has small-constant open leaves, while the shifted certificate is complete.

This is a local holdout exclusion, not a #429 decision or a BB(6) bound.
-/

namespace BB429Branch29Extra1024

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def cutResidues : List Nat := [15,47,79,191,255,383,447,639]
private def cutTargets : List BB429.State :=
  cutResidues.map (fun q => (32*q+29,64*q+55))

/-- One pass along the genuine source orbit excludes all eight small cylinder
representatives. -/
private def avoidMany (targets : List BB429.State) : Nat → BB429.State → Bool
  | 0, s => decide (s ∉ targets)
  | k+1, s => decide (s ∉ targets) &&
      match BB429.next s with
      | none => true
      | some t => avoidMany targets k t

private theorem avoidMany_to_avoid (targets : List BB429.State)
    (target : BB429.State) (hm : target ∈ targets)
    (k : Nat) (s : BB429.State)
    (h : avoidMany targets k s = true) :
    BB429FiniteAvoidance.avoid target k s = true := by
  induction k generalizing s with
  | zero =>
    simp only [avoidMany, BB429FiniteAvoidance.avoid] at h ⊢
    have hnot : s ∉ targets := of_decide_eq_true h
    exact decide_eq_true (by intro he; exact hnot (he ▸ hm))
  | succ k ih =>
    simp only [avoidMany] at h
    have hparts := Bool.and_eq_true_iff.mp h
    have hnot : s ∉ targets := of_decide_eq_true hparts.1
    simp only [BB429FiniteAvoidance.avoid]
    apply Bool.and_eq_true_iff.mpr
    constructor
    · exact decide_eq_true (by intro he; exact hnot (he ▸ hm))
    · cases hn : BB429.next s with
      | none => simp
      | some t =>
        have hh : avoidMany targets k t = true := by simpa [hn] using hparts.2
        simpa [hn] using ih t hh

private theorem root_prefix :
    BB429.run 19599 (0,0) = some (32801,16305) := by
  decide +kernel

private theorem root_avoids : avoidMany cutTargets 19599 (0,0) = true := by
  decide +kernel

/-- These eight fixed states cannot occur at ANY time in the true
blank-root accelerator. The finite computation is extended to all time
using the monotonic rank, not a finite-horizon assumption. -/
private theorem small_cut (q : Nat) (hq : q ∈ cutResidues) :
    ¬BB429NewResidue.Reach (32*q+29) (64*q+55) := by
  have hqbound : q ≤ 639 := by
    simp [cutResidues] at hq
    rcases hq with h|h|h|h|h|h|h|h <;> omega
  have hmem : (32*q+29,64*q+55) ∈ cutTargets := by
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  have havoid := avoidMany_to_avoid cutTargets (32*q+29,64*q+55)
    hmem 19599 (0,0) root_avoids
  have hrank : BB429.rank (32*q+29,64*q+55) <
      BB429.rank (32801,16305) := by
    simp only [BB429.rank]
    omega
  exact BB429FiniteAvoidance.no_reach_of_avoid
    (32*q+29,64*q+55) 19599 (0,0) (32801,16305)
    root_prefix havoid hrank

private def shifted (r : Nat) : BB429Kernel.Affine :=
  ⟨32768,32*(1024+r)+29,65536,64*(1024+r)+55⟩

/-- Eight complete infinite affine inverse-tree certificates. The base
parameter is shifted by 1024 so every symbolic inverse predecessor is
above the positive-source threshold. -/
private theorem shifted_cert :
    cutResidues.all (fun r => BB429Kernel.cert 12 (shifted r)) = true := by
  decide +kernel

private theorem large_cut (q r : Nat) (hr : q % 1024 = r)
    (hq : 1024 ≤ q) (hmem : r ∈ cutResidues) :
    ¬BB429NewResidue.Reach (32*q+29) (64*q+55) := by
  let t := q / 1024 - 1
  have hqeq : q = 1024*(t+1)+r := by dsimp [t]; omega
  have hx : BB429Kernel.va (shifted r) t = 32*q+29 := by
    simp only [BB429Kernel.va,shifted]
    omega
  have hy : BB429Kernel.vb (shifted r) t = 64*q+55 := by
    simp only [BB429Kernel.vb,shifted]
    omega
  have hc : BB429Kernel.cert 12 (shifted r) = true :=
    (List.all_eq_true.mp shifted_cert) r hmem
  intro hroot
  have hs : BB429NewResidue.Reach
      (BB429Kernel.va (shifted r) t) (BB429Kernel.vb (shifted r) t) := by
    simpa only [hx,hy] using hroot
  exact (BB429Kernel.cert_sound 12 (shifted r) t hc) hs

/-- New all-time theorem: eight whole q(mod1024) cylinders on branch29
are unreachable from blank. Unlike bounded-signed evidence, this applies
to every q, including q<1024 and arbitrarily large q. -/
theorem eight_cylinders_unreachable (q : Nat)
    (hq : q % 1024 ∈ cutResidues) :
    ¬BB429NewResidue.Reach (32*q+29) (64*q+55) := by
  by_cases hsmall : q < 1024
  · have heq : q % 1024 = q := Nat.mod_eq_of_lt hsmall
    exact small_cut q (heq ▸ hq)
  · exact large_cut q (q % 1024) rfl (by omega) hq

#print axioms eight_cylinders_unreachable
end BB429Branch29Extra1024
