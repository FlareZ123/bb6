import PartialAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32AuditReweight
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def quickWeight (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  if n+6≤B then true else weightOK p s n B

theorem quickWeight_sound {B p n s} (h : quickWeight B p n s = true) : weightOK p s n B = true := by
  unfold quickWeight at h
  split at h
  · rename_i hmargin
    unfold weightOK
    apply List.all_eq_true.mpr
    intro d hd
    have hd' := (List.mem_filter.mp hd).1
    have hlt : d < 6 := List.mem_range.mp hd'
    exact decide_eq_true (by omega)
  · exact h

theorem query_reweight {A B p n s} (h : zipQueryOK A p n s = true)
    (hw : quickWeight B p n s = true) : zipQueryOK B p n s = true := by
  simp only [zipQueryOK, Bool.and_eq_true] at h ⊢
  exact ⟨h.1,h.2.1,quickWeight_sound hw⟩

def weightAudit (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => quickWeight B p n s
  | .split n s kids => quickWeight B p n s && allMoves (fun mv => weightAudit B (refine p s (some mv)) (kids mv))
  | _ => true
termination_by structural t => t

theorem zip_reweight (A B : Nat) (p : PartialMachine) (t : Audit)
    (h : zipCheck A p t = true) (hw : weightAudit B p t = true) : zipCheck B p t = true := by
  induction t generalizing p with
  | last n s =>
    simp only [zipCheck, Bool.and_eq_true] at h ⊢
    exact ⟨query_reweight h.1 hw,h.2⟩
  | cycle => exact h
  | far => exact h
  | proven => exact h
  | split n s kids ih =>
    simp only [zipCheck, Bool.and_eq_true] at h ⊢
    simp only [weightAudit, Bool.and_eq_true] at hw
    exact ⟨query_reweight h.1 hw.1, allMoves_of _ (fun mv => ih mv _ (allMoves_sound _ h.2 mv) (allMoves_sound _ hw.2 mv))⟩

def partialWeights (B : Nat) (p : PartialMachine) : (t : PartialAudit) → Bool
  | .unresolved => true
  | .closed t => weightAudit B p t
  | .split n s kids => quickWeight B p n s && allMoves (fun mv => partialWeights B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem partial_reweight (A B : Nat) (p : PartialMachine) (t : PartialAudit)
    (h : partialCheck A p t = true) (hw : partialWeights B p t = true) : partialCheck B p t = true := by
  induction t generalizing p with
  | unresolved => rfl
  | closed t => exact zip_reweight A B p t h hw
  | split n s kids ih =>
    simp only [partialCheck, Bool.and_eq_true] at h ⊢
    simp only [partialWeights, Bool.and_eq_true] at hw
    exact ⟨query_reweight h.1 hw.1, allMoves_of _ (fun mv => ih mv _ (allMoves_sound _ h.2 mv) (allMoves_sound _ hw.2 mv))⟩
#print axioms quickWeight_sound
#print axioms zip_reweight
#print axioms partial_reweight
end BB6.Agent32AuditReweight
