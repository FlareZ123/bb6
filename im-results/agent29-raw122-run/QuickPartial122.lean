import QuickWeight
set_option maxHeartbeats 0
namespace BB6.Agent29ResidualCover
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6.Agent43QuickWeight

def quickPartial (B : Nat) (p : PartialMachine) : (t : PartialAudit) → Bool
  | .unresolved => true
  | .closed a => quickPrefix B p a
  | .split n s kids => quickZipQuery B p n s && allMoves (fun mv => quickPartial B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem quickPartial_eq (B : Nat) (p : PartialMachine) (t : PartialAudit) : quickPartial B p t = partialCheck B p t := by
  induction t generalizing p with
  | unresolved => rfl
  | closed a => rw [quickPartial,partialCheck.eq_2,quickPrefix_eq]
  | split n s kids ih =>
    rw [quickPartial,partialCheck.eq_3,quickZipQuery_eq]
    apply congrArg (fun x => zipQueryOK B p n s && x)
    apply congrArg allMoves
    funext mv
    exact ih mv _
#print axioms quickPartial_eq
end BB6.Agent29ResidualCover
