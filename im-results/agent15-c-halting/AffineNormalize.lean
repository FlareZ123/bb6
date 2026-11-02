import ReachAffine
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

def CReach (a k : Nat) : Prop :=
    ∃ time : Nat, BB6.Agent8Section.run secNext time (some (5,1))=some (a,k)

/-- Normalize a Machine C section by successively stripping every forced
    affine predecessor. The right counter strictly decreases each round. -/
def affineNormalize (a k : Nat) : Nat × Nat :=
  if h : 4≤k ∧ k%2=0 ∧ (a+k)%4=1 then
    affineNormalize (a+k-2) ((k-2)/2)
  else (a,k)
termination_by k
decreasing_by
  omega

/-- The normalizer preserves and reflects exact authentic blank-orbit
    reachability for every arbitrary natural section input. -/
theorem reach_iff_normalize (a k : Nat) :
    CReach a k ↔ CReach (affineNormalize a k).1 (affineNormalize a k).2 := by
  induction k using Nat.strongRecOn generalizing a with
  | ind k ih =>
      by_cases hc : 4≤k ∧ k%2=0 ∧ (a+k)%4=1
      · have hdec : (k-2)/2<k := by omega
        have hrec := ih _ hdec (a+k-2)
        have hstep : CReach a k ↔ CReach (a+k-2) ((k-2)/2) :=
          blank_reach_iff_affine a k hc.1 hc.2.1 hc.2.2
        rw [affineNormalize, dif_pos hc]
        exact hstep.trans hrec
      · rw [affineNormalize, dif_neg hc]

#print axioms reach_iff_normalize
end BB6.Agent15
