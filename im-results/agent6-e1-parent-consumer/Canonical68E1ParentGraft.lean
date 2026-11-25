import Canonical74Raw109Raw123Graft
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent6Canonical68E1ParentGraft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31Canonical74Raw109Raw123

/-- The common E1 prefix before its six-symbol branch is assigned. -/
abbrev e1Base : PartialMachine := (pathEnd root 2 (path.take 4)).1

/-- The six additional source-accepted E1 sibling parents. -/
abbrev p60 : PartialMachine := refine e1Base (4,true) (some ⟨true,true,0⟩)
abbrev p110 : PartialMachine := refine e1Base (4,true) (some ⟨false,false,2⟩)
abbrev p111 : PartialMachine := refine e1Base (4,true) (some ⟨false,true,2⟩)
abbrev p117 : PartialMachine := refine e1Base (4,true) (some ⟨true,true,3⟩)
abbrev p121 : PartialMachine := refine e1Base (4,true) (some ⟨true,true,4⟩)
abbrev p125 : PartialMachine := refine e1Base (4,true) (some ⟨true,true,5⟩)

/-- Every parent starts with the standard first-one transition. -/
theorem p60_root : p60 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p110_root : p110 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p111_root : p111 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p117_root : p117 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p121_root : p121 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p125_root : p125 initialSlot = some (some ⟨true,true,1⟩) := by decide

/-- Exact sameTable membership in the roster after Raw109 and Raw123. -/
theorem p60_parent_count :
    (roster74.filter (fun e => sameTable e.2 p60)).length = 1 := by decide

noncomputable def roster73 := graftRoster p60 [] roster74
theorem count73 : roster73.length = 73 := by decide

theorem p110_parent_count :
    (roster73.filter (fun e => sameTable e.2 p110)).length = 1 := by decide

noncomputable def roster72 := graftRoster p110 [] roster73
theorem count72 : roster72.length = 72 := by decide

theorem p111_parent_count :
    (roster72.filter (fun e => sameTable e.2 p111)).length = 1 := by decide

noncomputable def roster71 := graftRoster p111 [] roster72
theorem count71 : roster71.length = 71 := by decide

theorem p117_parent_count :
    (roster71.filter (fun e => sameTable e.2 p117)).length = 1 := by decide

noncomputable def roster70 := graftRoster p117 [] roster71
theorem count70 : roster70.length = 70 := by decide

theorem p121_parent_count :
    (roster70.filter (fun e => sameTable e.2 p121)).length = 1 := by decide

noncomputable def roster69 := graftRoster p121 [] roster70
theorem count69 : roster69.length = 69 := by decide

theorem p125_parent_count :
    (roster69.filter (fun e => sameTable e.2 p125)).length = 1 := by decide

noncomputable def roster68 := graftRoster p125 [] roster69
theorem count68 : roster68.length = 68 := by decide

/-- Lift a source-accepted parent Cover to the common raw110 binding floor. -/
theorem lift_parent_cover {C : Nat} {p : PartialMachine}
    (hC : C ≤ 6766859) (h : Cover (WeightedBound C) p) :
    ∀ m, compatible p m → WeightedBound 6766859 m := by
  intro m hm k d hk hd
  exact Nat.le_trans (h.sound m hm k d hk hd) hC

/-- Consume the Raw60 parent, leaving 73 exact quotient representatives. -/
theorem sound73
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster73, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p60) (replacement := []) (roster := roster74)
    p60_root (BB6.Agent31Canonical74Raw109Raw123.sound h109 h123)
  intro m hm
  exact Or.inl (lift_parent_cover (by decide) h60 m hm)

/-- Consume Raw110, whose 6,766,859 bound is the binding floor. -/
theorem sound72
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60)
    (h110 : Cover (WeightedBound 6766859) p110) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster72, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p110) (replacement := []) (roster := roster73)
    p110_root (sound73 h109 h123 h60)
  intro m hm
  exact Or.inl (h110.sound m hm)

/-- Consume Raw111 at its accepted 7,014 bound. -/
theorem sound71
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60)
    (h110 : Cover (WeightedBound 6766859) p110)
    (h111 : Cover (WeightedBound 7014) p111) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster71, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p111) (replacement := []) (roster := roster72)
    p111_root (sound72 h109 h123 h60 h110)
  intro m hm
  exact Or.inl (lift_parent_cover (by decide) h111 m hm)

/-- Consume Raw117 at its accepted 1,291 bound. -/
theorem sound70
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60)
    (h110 : Cover (WeightedBound 6766859) p110)
    (h111 : Cover (WeightedBound 7014) p111)
    (h117 : Cover (WeightedBound 1291) p117) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster70, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p117) (replacement := []) (roster := roster71)
    p117_root (sound71 h109 h123 h60 h110 h111)
  intro m hm
  exact Or.inl (lift_parent_cover (by decide) h117 m hm)

/-- Consume Raw121 at its accepted 4,063 bound. -/
theorem sound69
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60)
    (h110 : Cover (WeightedBound 6766859) p110)
    (h111 : Cover (WeightedBound 7014) p111)
    (h117 : Cover (WeightedBound 1291) p117)
    (h121 : Cover (WeightedBound 4063) p121) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster69, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p121) (replacement := []) (roster := roster70)
    p121_root (sound70 h109 h123 h60 h110 h111 h117)
  intro m hm
  exact Or.inl (lift_parent_cover (by decide) h121 m hm)

/-- Consume Raw125 at its accepted 1,290 bound. -/
theorem sound68
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60)
    (h110 : Cover (WeightedBound 6766859) p110)
    (h111 : Cover (WeightedBound 7014) p111)
    (h117 : Cover (WeightedBound 1291) p117)
    (h121 : Cover (WeightedBound 4063) p121)
    (h125 : Cover (WeightedBound 1290) p125) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster68, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p125) (replacement := []) (roster := roster69)
    p125_root (sound69 h109 h123 h60 h110 h111 h117 h121)
  intro m hm
  exact Or.inl (lift_parent_cover (by decide) h125 m hm)

/-- Conditional exactness after all eight E1 parent Covers. The 68 retained
    quotient representatives remain explicit and unresolved. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60)
    (h110 : Cover (WeightedBound 6766859) p110)
    (h111 : Cover (WeightedBound 7014) p111)
    (h117 : Cover (WeightedBound 1291) p117)
    (h121 : Cover (WeightedBound 4063) p121)
    (h125 : Cover (WeightedBound 1290) p125)
    (hLeaves : ∀ e ∈ roster68, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB
    (sound68 h109 h123 h60 h110 h111 h117 h121 h125)
    hLeaves champ

#print axioms p60_parent_count
#print axioms p110_parent_count
#print axioms p111_parent_count
#print axioms p117_parent_count
#print axioms p121_parent_count
#print axioms p125_parent_count
#print axioms count73
#print axioms count72
#print axioms count71
#print axioms count70
#print axioms count69
#print axioms count68
#print axioms sound68
#print axioms exact_at_target

end BB6.Agent6Canonical68E1ParentGraft
