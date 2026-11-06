import BB429Count52
import BB429ManyLifts
import BB429FiveShift
import Lean.Elab.Tactic.Omega

namespace BB429Count58Sixteen
/-- Necessary terminal classes modulo 16384 after composing the source-verified
    52/8192 predicate, Agent30's 41 exclusions and Agent33's five new rays. -/
def live58 : List Nat :=
  [9,337,465,765,1097,1141,1673,1789,1973,2057,2165,2385,
   2513,2685,2897,3081,3145,3189,3281,4169,4341,4661,4733,5045,
   5457,6141,6345,6389,6709,7093,7817,7933,8061,8757,9041,9425,
   10441,10449,10705,11089,11601,12157,12213,12405,12489,12497,
   12533,12925,13137,13309,13321,14205,14409,14901,15101,15357,
   16009,16381]

theorem live58_count : live58.length = 58 := by decide
theorem live58_nodup : live58.Nodup := by decide

private def keep (r : Nat) : Prop :=
    r ∈ live58 ↔ (r%8192 ∈ BB429Count52.live52 ∧
      r ∉ BB429ManyLifts.newLifts ∧ r ≠ 11473 ∧
      r ∉ BB429FiveShift.excludedFive)

private instance (r : Nat) : Decidable (keep r) := by
  unfold keep
  infer_instance

/-- The explicit 58 representative integers all satisfy the combined mask. -/
private theorem live_good :
    live58.all (fun r => decide (r < 16384 ∧ keep r)) = true := by decide

/-- Check the two possible lifts of each of the 52 source-proved 8192 classes. -/
private theorem low_lift :
    BB429Count52.live52.all (fun r => decide (keep r)) = true := by decide

private theorem high_lift :
    BB429Count52.live52.all (fun r => decide (keep (8192+r))) = true := by decide

/-- The *exact* combined arithmetic mask for every natural terminal counter.
    The proof reduces all 16384 residues to 52 pairs of lifts. -/
theorem live58_iff (u : Nat) :
    u%16384 ∈ live58 ↔
      u%8192 ∈ BB429Count52.live52 ∧
      u%16384 ∉ BB429ManyLifts.newLifts ∧
      u%16384 ≠ 11473 ∧
      u%16384 ∉ BB429FiveShift.excludedFive := by
  have hm : (u%16384)%8192 = u%8192 := by omega
  constructor
  · intro hl
    have h := of_decide_eq_true ((List.all_eq_true.mp live_good) (u%16384) hl)
    exact hm ▸ (h.2.mp hl)
  · intro hg
    let r := u%8192
    have hr : r ∈ BB429Count52.live52 := by simpa only [r] using hg.1
    have hmod : (u%16384 = r) ∨ (u%16384 = 8192+r) := by
      dsimp [r]
      omega
    rcases hmod with h0 | h1
    · have hp : keep r := of_decide_eq_true ((List.all_eq_true.mp low_lift) r hr)
      rw [h0] at hg ⊢
      exact hp.mpr (by simpa [keep, r] using hg)
    · have hp : keep (8192+r) :=
        of_decide_eq_true ((List.all_eq_true.mp high_lift) r hr)
      rw [h1] at hg ⊢
      exact hp.mpr (by simpa [keep, r] using hg)

#print axioms live58_count
#print axioms live58_nodup
#print axioms live58_iff
end BB429Count58Sixteen
