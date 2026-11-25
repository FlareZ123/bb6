import IncrementalAudit
import Root109Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent14B01LCGraft

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent13CrossRouteHeldLeaf109

abbrev Parent : PartialMachine := firstOneB0_1LC

/-- Attach membership proofs to the exact 65 side-witness cylinders already
    shown to refine the B0=1LC obligation. -/
abbrev WitnessEntry :=
  { w : BB6.Agent47SevenSideWitnesses.SideWitness //
      w ∈ b0_1lcSideWitnesses }

def witnessEntries : List WitnessEntry := b0_1lcSideWitnesses.attach

theorem witnessEntries_count : witnessEntries.length = 65 := by
  simp [witnessEntries, b0_1lcSideWitnesses_count]

/-- Weighted safety is monotone in the target bound. -/
theorem weightedBound_mono {B C : Nat} {m : Machine}
    (hBC : B ≤ C) (h : WeightedBound B m) : WeightedBound C m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hBC

/-- Every selected side-witness cylinder is a complete Cover at any bound
    at least 7014, using its already checked side-cycle invariant. -/
def witnessCover {B : Nat} (hB : 7014 ≤ B) (e : WitnessEntry) :
    Cover (WeightedBound B) (unpackTable e.val.table) :=
  .leaf _ (by
    intro m hm
    exact weightedBound_mono hB
      (b0_1lcSideWitnesses_safe e.val e.property m hm))

/-- Sequentially graft every one of the 65 authenticated cylinders into the
    parent audit. The generic graft branches only where a source-fixed slot
    is not already fixed, and leaves every incompatible completion open. -/
noncomputable def graftAll {B : Nat} (hB : 7014 ≤ B) :
    List WitnessEntry →
      FrontierAudit (WeightedBound B) Parent →
      FrontierAudit (WeightedBound B) Parent
  | [], audit => audit
  | e :: es, audit =>
      graftAll hB es
        (addCertificate audit (unpackTable e.val.table) (witnessCover hB e))

noncomputable def witnessAudit (B : Nat) (hB : 7014 ≤ B) :
    FrontierAudit (WeightedBound B) Parent :=
  graftAll hB witnessEntries (.unresolved Parent)

/-- Exact semantics of the sequential graft: a machine remains open precisely
    when it was open before and fails to match every newly grafted cylinder. -/
theorem graftAll_open_iff {B : Nat} (hB : 7014 ≤ B)
    (es : List WitnessEntry) (audit : FrontierAudit (WeightedBound B) Parent)
    (m : Machine) (hm : compatible Parent m) :
    (graftAll hB es audit).open m ↔
      audit.open m ∧
        ∀ e ∈ es, ¬ compatible (unpackTable e.val.table) m := by
  induction es generalizing audit with
  | nil =>
      simp [graftAll]
  | cons e es ih =>
      change (graftAll hB es
        (addCertificate audit (unpackTable e.val.table) (witnessCover hB e))).open m ↔
        audit.open m ∧
          ∀ e' ∈ e :: es, ¬ compatible (unpackTable e'.val.table) m
      rw [ih (addCertificate audit (unpackTable e.val.table) (witnessCover hB e))]
      rw [addCertificate_open_iff audit (unpackTable e.val.table)
        (witnessCover hB e) m hm]
      constructor
      · rintro ⟨⟨ha, hhead⟩, htail⟩
        refine ⟨ha, ?_⟩
        intro e' he'
        rcases List.mem_cons.mp he' with rfl | hmem
        · exact hhead
        · exact htail e' hmem
      · rintro ⟨ha, hall⟩
        refine ⟨⟨ha, hall e (by simp)⟩, ?_⟩
        intro e' he'
        exact hall e' (by simp [he'])

/-- The 65-way graft's open set is exactly the complement of the union of the
    selected side-witness cylinders inside the B0=1LC parent. -/
theorem witnessAudit_open_iff {B : Nat} (hB : 7014 ≤ B)
    (m : Machine) (hm : compatible Parent m) :
    (witnessAudit B hB).open m ↔
      ∀ e ∈ witnessEntries,
        ¬ compatible (unpackTable e.val.table) m := by
  unfold witnessAudit
  rw [graftAll_open_iff hB witnessEntries (.unresolved Parent) m hm]
  simp [FrontierAudit.open]

/-- Same complement characterization, stated over the original witness list
    rather than its attached subtype. -/
theorem witnessAudit_open_iff_sideWitnesses {B : Nat} (hB : 7014 ≤ B)
    (m : Machine) (hm : compatible Parent m) :
    (witnessAudit B hB).open m ↔
      ∀ w ∈ b0_1lcSideWitnesses,
        ¬ compatible (unpackTable w.table) m := by
  rw [witnessAudit_open_iff hB m hm]
  constructor
  · intro hall w hw
    have he : (⟨w, hw⟩ : WitnessEntry) ∈ witnessEntries := by
      simp [witnessEntries]
    exact hall ⟨w, hw⟩ he
  · intro hall e he
    rcases e with ⟨w, hw⟩
    exact hall w hw

/-- Every parent completion is either proved safe at B or retained in the
    explicit open complement. -/
theorem witnessAudit_exhaustive {B : Nat} (hB : 7014 ≤ B)
    (m : Machine) (hm : compatible Parent m) :
    WeightedBound B m ∨ (witnessAudit B hB).open m :=
  FrontierAudit.exhaustive (witnessAudit B hB) m hm

/-- Any completion matching one of the 65 accepted side-witness cylinders
    is closed by the consuming audit. -/
theorem witnessAudit_closes_sideWitness {B : Nat} (hB : 7014 ≤ B)
    (m : Machine) (hm : compatible Parent m)
    (w : BB6.Agent47SevenSideWitnesses.SideWitness)
    (hw : w ∈ b0_1lcSideWitnesses)
    (hwitness : compatible (unpackTable w.table) m) :
    ¬ (witnessAudit B hB).open m := by
  intro hopen
  exact (witnessAudit_open_iff_sideWitnesses hB m hm).mp hopen w hw hwitness

/-- The exact B0=1LC parent has ten free transitions. -/
theorem parent_freeSlotCount : freeSlotCount Parent = 10 := by
  decide [Parent, firstOneB0_1LC, BB6.Agent50TNFPilot.root, refine, emptyTable]

theorem parent_cylinderMass : cylinderMass Parent = 25 ^ 10 := by
  unfold cylinderMass
  rw [parent_freeSlotCount]

/-- The proof-carrying audit partitions all 25^10 parent completions into
    certified and explicitly open terminal cylinders; no complement is lost. -/
theorem witnessAudit_mass_conserves {B : Nat} (hB : 7014 ≤ B) :
    (witnessAudit B hB).report.1 + (witnessAudit B hB).report.2 = 25 ^ 10 := by
  rw [← parent_cylinderMass]
  exact FrontierAudit.report_conserves (witnessAudit B hB)

/-- Each grafted witness is genuinely a subcylinder of the exact 109-roster
    parent, not merely a compatible table in a text export. -/
theorem sideWitness_refines_parent (e : WitnessEntry) :
    refinesMachine (unpackTable e.val.table) Parent := by
  apply refinesMachineB_sound
  exact (List.mem_filter.mp e.property).2

/-- The parent being refined is the exact B0=1LC member of the retained
    109-entry roster. -/
theorem parent_is_exact_109_member :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      BB6.Agent31FourHoleRoster.sameTable e.2 Parent = true := by
  exact sourceHeldParent_is_exact_109_member

#print axioms weightedBound_mono
#print axioms witnessCover
#print axioms graftAll_open_iff
#print axioms witnessAudit_open_iff_sideWitnesses
#print axioms witnessAudit_exhaustive
#print axioms witnessAudit_closes_sideWitness
#print axioms witnessAudit_mass_conserves
#print axioms sideWitness_refines_parent
#print axioms parent_is_exact_109_member

end BB6.Agent14B01LCGraft
