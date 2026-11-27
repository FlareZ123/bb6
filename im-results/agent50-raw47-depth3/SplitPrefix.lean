import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50SplitPrefix
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit

theorem allMoves_true {f : Move → Bool} (h : ∀ mv, f mv = true) : allMoves f = true := by
  simp [allMoves, h]

theorem split_checked {B : Nat} {p : PartialMachine} {n : Nat} {s : Slot} {kids : Move → Audit}
    (hq : zipQueryOK B p n s = true)
    (hk : ∀ mv, prefixCheck B (refine p s (some mv)) (kids mv) = true) :
    prefixCheck B p (.split n s kids) = true := by
  rw [prefixCheck_eq,zipCheck.eq_5,hq]
  simp only [Bool.true_and]
  apply allMoves_true
  intro mv
  rw [← prefixCheck_eq]
  exact hk mv
#print axioms split_checked
end BB6.Agent50SplitPrefix
