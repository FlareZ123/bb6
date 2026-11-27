import Raw14086B
import Raw14086Entry
import BlockFARBridge
import ZipThreeHoleAudit
namespace Raw14086
open BB6BlockFAR Raw140Orbit Raw140Extra Raw14086Local Raw14086Arithmetic
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] BB6BlockFAR.run boundary
theorem return_sound (k : Kind) (p : Nat) (hp : 24 ≤ p) : Plus (cfg (k,p)) (cfg (ret k p)) := by
  cases k with
  | a0 => exact a0Return p hp
  | a2 => exact a2Return p hp
  | b0 => exact b0Return p hp

theorem infinite (c : Cfg) (hc : 24 ≤ c.2) (k : Nat) : ∃ x, run M86 k (cfg c) = some x := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    obtain ⟨n,hn,h⟩ := return_sound c.1 c.2 hc
    have hg := ret_growth c.1 c.2 hc
    by_cases hle : n ≤ k
    · obtain ⟨x,hx⟩ := ih (k-n) (by omega) (ret c.1 c.2) (by omega)
      exact ⟨x,by rw [show k=n+(k-n) by omega,run_add,h]; exact hx⟩
    · rw [show n=k+(n-k) by omega,run_add] at h
      cases he : run M86 k (cfg c) with
      | none => simp [he] at h
      | some x => exact ⟨x,rfl⟩
theorem forever (k : Nat) : ∃ x, run M86 k primBlank = some x := by
  have h := entry
  by_cases hle : 6892 ≤ k
  · obtain ⟨x,hx⟩ := infinite (.a2,39) (by decide) (k-6892)
    exact ⟨x,by rw [show k=6892+(k-6892) by omega,run_add,h]; exact hx⟩
  · rw [show 6892=k+(6892-k) by omega,run_add] at h
    cases he : run M86 k primBlank with
    | none => simp [he] at h
    | some x => exact ⟨x,rfl⟩

def p : PartialMachine := FAR.fromCodes [7,23,11,12,15,1,6,18,4,17,11,24]
theorem table_eq : BB6BlockFAR.partialTable M86 = p := tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6BlockFAR.transfer_never M86 m (by rwa [table_eq]) forever
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms return_sound
#print axioms entry
#print axioms never
#print axioms cover
end Raw14086
