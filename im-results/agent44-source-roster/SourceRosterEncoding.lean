import RosterConvergence

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent44SourceRoster

open BB6Coverage
open BB6.Agent50RootFrontier
open BB6.Agent13RosterConvergence

/-- A source Coq TM has one option layer: None is the wildcard/unassigned
    row in is_child_of. The Lean partial machine has two layers, so a fixed
    halt (some none) must not be silently collapsed into a hole (none). -/
def noAssignedHalt (t : PackedTable) : Bool :=
  (List.finRange 6).all fun q =>
    [false, true].all fun b =>
      decide (unpackTable t (q,b) ≠ some none)

/-- The exact 124-table canonical residual roster contains no assigned halt
    rows. Thus its holes are exactly the rows encoded as "---" by the source
    TM serializer; no fixed HALT row is erased by the one-option Coq type. -/
theorem canonicalResidualRoster_noAssignedHalt :
    canonicalResidualRoster.all noAssignedHalt = true := by
  decide

theorem canonicalResidualRoster_noAssignedHalt_at
    {t : PackedTable} (ht : t ∈ canonicalResidualRoster) :
    ∀ s, unpackTable t s ≠ some none := by
  intro s
  rcases s with ⟨q,b⟩
  have ht' : noAssignedHalt t = true :=
    List.all_eq_true.mp canonicalResidualRoster_noAssignedHalt t ht
  unfold noAssignedHalt at ht'
  have hq := List.all_eq_true.mp ht' q (List.mem_finRange q)
  have hb := List.all_eq_true.mp hq b (by cases b <;> simp)
  exact decide_eq_true_eq.mp hb

/-- Forget only unassigned slots, yielding the partial TM convention used by
    the original Coq source: a None row is a wildcard in is_child_of. -/
def forgetUnassigned (p : PartialMachine) : Machine :=
  fun s => (p s).getD none

def sourceParentOfPacked (t : PackedTable) : Machine :=
  forgetUnassigned (unpackTable t)

/-- Lean mirror of the original source relation:
    a parent None row is unconstrained; every parent Some row is fixed. -/
def sourceChildOf (child parent : Machine) : Prop :=
  ∀ s, parent s = none ∨ parent s = child s

theorem compatible_iff_sourceChildOf
    (p : PartialMachine) (m : Machine)
    (hNoHalt : ∀ s, p s ≠ some none) :
    compatible p m ↔ sourceChildOf m (forgetUnassigned p) := by
  constructor
  · intro h s
    cases hp : p s with
    | none =>
        left
        simp [forgetUnassigned, hp]
    | some t =>
        have ht : t ≠ none := by
          intro htn
          exact hNoHalt s (by simp [hp, htn])
        right
        have hm := h s t hp
        simp [forgetUnassigned, hp, hm]
  · intro h s t hp
    have ht : t ≠ none := by
      intro htn
      exact hNoHalt s (by simp [hp, htn])
    have hnot : forgetUnassigned p s ≠ none := by
      simp [forgetUnassigned, hp, ht]
    rcases h s with hnone | heq
    · exact (hnot hnone).elim
    · have hval : forgetUnassigned p s = t := by
        simp [forgetUnassigned, hp]
      have hm : t = m s := hval.symm.trans heq
      exact hm.symm

theorem canonicalResidualRoster_compatible_iff
    {t : PackedTable} (ht : t ∈ canonicalResidualRoster) (m : Machine) :
    compatible (unpackTable t) m ↔ sourceChildOf m (sourceParentOfPacked t) :=
  compatible_iff_sourceChildOf (unpackTable t) m
    (canonicalResidualRoster_noAssignedHalt_at ht)

/-- The source TM serializer uses "---" for None and the same 0/1, L/R,
    A-F transition triples as RootFrontier.encodeTable. -/
def encodeSourceTransition : Transition → String
  | none => "---"
  | some mv => BB6.Agent50RootFrontier.encodeMove mv

def encodeSourceMachine (m : Machine) : String :=
  String.intercalate "_" ((List.finRange 6).map fun q =>
    encodeSourceTransition (m (q,false)) ++
    encodeSourceTransition (m (q,true)))

theorem encodeTable_forgetUnassigned
    (p : PartialMachine) (hNoHalt : ∀ s, p s ≠ some none) :
    BB6.Agent50RootFrontier.encodeTable p =
      encodeSourceMachine (forgetUnassigned p) := by
  have hcell (s : Slot) :
      BB6.Agent50RootFrontier.encodeTransition (p s) =
        encodeSourceTransition (forgetUnassigned p s) := by
    cases hp : p s with
    | none =>
        simp [BB6.Agent50RootFrontier.encodeTransition,
          encodeSourceTransition, forgetUnassigned, hp]
    | some t =>
        cases t with
        | none =>
            exact (hNoHalt s (by simpa [hp])).elim
        | some mv =>
            simp [BB6.Agent50RootFrontier.encodeTransition,
              encodeSourceTransition, forgetUnassigned, hp,
              BB6.Agent50RootFrontier.encodeMove]
  unfold BB6.Agent50RootFrontier.encodeTable encodeSourceMachine
  congr 1
  apply List.map_congr_left
  intro q hq
  simp only [hcell (q,false), hcell (q,true)]

theorem canonicalResidualRoster_encode_eq
    {t : PackedTable} (ht : t ∈ canonicalResidualRoster) :
    BB6.Agent50RootFrontier.encodeTable (unpackTable t) =
      encodeSourceMachine (sourceParentOfPacked t) :=
  encodeTable_forgetUnassigned (unpackTable t)
    (canonicalResidualRoster_noAssignedHalt_at ht)

#print axioms canonicalResidualRoster_noAssignedHalt
#print axioms canonicalResidualRoster_compatible_iff
#print axioms canonicalResidualRoster_encode_eq

end BB6.Agent44SourceRoster
