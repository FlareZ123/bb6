import IncrementalAuditReport
import CertificateBatchReport

namespace BB6Coverage

/-- Every slot assigned in the parent is assigned the same value in the child. -/
def extendsCheck (parent child : PartialMachine) : Bool :=
  auditSlots.all fun s => match parent s with
    | none => true
    | some t => decide (child s = some t)

theorem extendsCheck_sound {p q : PartialMachine} (h : extendsCheck p q = true)
    {m : Machine} (hm : compatible q m) : compatible p m := by
  intro s t ht
  have hs := List.all_eq_true.mp h s (auditSlots_complete s)
  simp [ht] at hs
  exact hm s t hs

/-- Two cylinders conflict exactly when some shared assigned slot disagrees. -/
def conflictCheck (p q : PartialMachine) : Bool :=
  auditSlots.any fun s => match p s, q s with
    | some t, some u => decide (t ≠ u)
    | _, _ => false

theorem conflictCheck_sound {p q : PartialMachine} (h : conflictCheck p q = true)
    {m : Machine} (hm : compatible p m) : ¬ compatible q m := by
  obtain ⟨s, _, hs⟩ := List.any_eq_true.mp h
  cases hp : p s with
  | none => simp [hp] at hs
  | some t =>
    cases hq : q s with
    | none => simp [hp, hq] at hs
    | some u =>
      simp [hp, hq] at hs
      exact incompatible_of_slot_conflict s t u hp hq hs m hm

/-- A small quadratic disjointness checker; never enumerates full tables. -/
def pairwiseConflictCheck : List PartialMachine → Bool
  | [] => true
  | p :: ps => (ps.all fun q => conflictCheck q p) && pairwiseConflictCheck ps

theorem pairwiseConflictCheck_sound {good : Machine → Prop}
    (cs : List (LeafCertificate good))
    (h : pairwiseConflictCheck (cs.map Subtype.val) = true) :
    PairwiseCertificateDisjoint cs := by
  induction cs with
  | nil => exact List.Pairwise.nil
  | cons c cs ih =>
    simp only [List.map_cons, pairwiseConflictCheck, Bool.and_eq_true] at h
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih h.2⟩
    intro d hd m hm
    exact conflictCheck_sound (List.all_eq_true.mp h.1 d.val (List.mem_map.mpr ⟨d, hd, rfl⟩)) hm

#print axioms extendsCheck_sound
#print axioms conflictCheck_sound
#print axioms pairwiseConflictCheck_sound
end BB6Coverage
