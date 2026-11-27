import PackedAudit
import FastThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3PackedAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit

def weightOnly (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => weightOK p s n B
  | .split n s kids => weightOK p s n B && allMoves (fun mv => weightOnly B (refine p s (some mv)) (kids mv))
  | _ => true
termination_by structural t => t

theorem query_replace_weight {B B' p n s} (h : packedQueryOK B p n s = true)
    (w : weightOK p s n B' = true) : packedQueryOK B' p n s = true := by
  simp only [packedQueryOK, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, h.2.1, w⟩

theorem packed_replace_weight (B B' : Nat) (p : PartialMachine) (t : Audit)
    (h : packedCheck B p t = true) (w : weightOnly B' p t = true) : packedCheck B' p t = true := by
  induction t generalizing p with
  | last n s =>
    simp only [packedCheck, Bool.and_eq_true] at h ⊢
    exact ⟨query_replace_weight h.1 w, h.2⟩
  | cycle e k r b => exact h
  | far rev d C => exact h
  | proven q safe => exact h
  | split n s kids ih =>
    simp only [packedCheck, Bool.and_eq_true] at h ⊢
    simp only [weightOnly, Bool.and_eq_true] at w
    refine ⟨query_replace_weight h.1 w.1, allMoves_of _ ?_⟩
    intro mv
    exact ih mv _ (allMoves_sound _ h.2 mv) (allMoves_sound _ w.2 mv)
#print axioms packed_replace_weight
end BB6.Agent3PackedAudit
