import SparseAudit
import DirectFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3DirectAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit
open BB6.Agent3PackedCycle BB6.Agent3SparseAudit

def directCheck (B : Nat) (p : PartialMachine) : (t : SparseAudit) → Bool
  | .last n s => packedQueryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleH p e k r b
  | .far rev _ C S => FAR.Direct.check C S (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => packedQueryOK B p n s &&
      allMoves (fun mv => directCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem directCheck_sparse (B : Nat) (p : PartialMachine) (t : SparseAudit)
    (h : directCheck B p t = true) : sparseCheck B p t = true := by
  induction t generalizing p with
  | last n s => exact h
  | cycle e k r b => exact h
  | far rev d C S =>
    exact FAR.Direct.check_sparse C S _ h
  | proven q safe => exact h
  | split n s kids ih =>
    have hc : packedQueryOK B p n s = true ∧
        allMoves (fun mv => directCheck B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [directCheck,Bool.and_eq_true] using h
    simp only [sparseCheck,Bool.and_eq_true]
    refine ⟨hc.1,allMoves_of _ ?_⟩
    intro mv
    exact ih mv _ (allMoves_sound _ hc.2 mv)

#print axioms directCheck_sparse
end BB6.Agent3DirectAudit
