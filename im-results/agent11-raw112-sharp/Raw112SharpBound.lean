import Raw112Reweight

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
The expected sharp global weighted score of the six-hole Raw112 parent is
91,503, not the accepted preliminary certificate threshold 100,000.

Kernel acceptance requires two actual computations on the *authentic*
25,004-split PartialAudit: weight test at 91,503 and failure at 91,502.
No external simulator or candidate JSON is trusted for these equations.
Once they compile, the parent iff from Raw112Reweight proves both a sharp
uniform bound and an attaining completion.
-/

namespace BB6.Agent11Raw112SharpBound

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47PartialAudit
open BB6.Agent32AuditReweight BB6.Agent11Raw112Reweight

def p := BB6.Agent47Raw112.parent
def t := BB6.Agent47Raw112.tree

theorem weights_91503 :
    partialWeights 91503 p t = true := by decide

theorem weights_91502 :
    partialWeights 91502 p t = false := by decide

theorem all_bound_91503 (m : Machine) (hm : compatible p m) :
    WeightedBound 91503 m := by
  exact (weighted_bound_iff_query_weights 91503).mpr weights_91503 m hm

theorem not_all_bound_91502 :
    ¬ (∀ m : Machine, compatible p m → WeightedBound 91502 m) := by
  intro h
  have hw := (weighted_bound_iff_query_weights 91502).mp h
  rw [weights_91502] at hw
  contradiction

/-- Exact sharp threshold of the entire 25^6-completion Raw112 parent. -/
theorem bound_iff (B : Nat) :
    (∀ m : Machine, compatible p m → WeightedBound B m) ↔ 91503 ≤ B := by
  constructor
  · intro hb
    by_contra hbad
    have hle : B ≤ 91502 := by omega
    have hsmall : ∀ m : Machine, compatible p m → WeightedBound 91502 m := by
      intro m hm k d hk hd
      have bound := hb m hm k d hk hd
      omega
    exact not_all_bound_91502 hsmall
  · intro hge m hm k d hk hd
    have h := all_bound_91503 m hm k d hk hd
    omega

/-- A compatible halting completion attains the sharp weighted score.
    The existence proof does not appeal to a computational witness outside
    Lean: if no attaining machine existed, the 91503 uniform upper bound
    would be strict and contradict the 91502 failure. -/
theorem attained :
    ∃ m : Machine, compatible p m ∧
      ∃ k d : Nat, HaltsAfter m k ∧
        d ∈ delays (zeroNext m) 0 ∧ d + k + 1 = 91503 := by
  classical
  apply Classical.byContradiction
  intro hnone
  apply not_all_bound_91502
  intro m hm k d hk hd
  have hb := all_bound_91503 m hm k d hk hd
  have hne : d + k + 1 ≠ 91503 := by
    intro he
    exact hnone ⟨m, hm, k, d, hk, hd, he⟩
  omega

#print axioms weights_91503
#print axioms weights_91502
#print axioms all_bound_91503
#print axioms not_all_bound_91502
#print axioms bound_iff
#print axioms attained
end BB6.Agent11Raw112SharpBound
