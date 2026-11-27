import CanonicalPartial

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50QuotientRefinement
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent47CanonicalFrontier

abbrev Entry := List Move × PartialMachine

/-- A checked refinement can discharge a cylinder, or replace it by its
    exact unresolved child cylinders. No positional roster matching is used. -/
structure Refinement (B : Nat) where
  parent : PartialMachine
  children : List Entry
  sound : ∀ m, TNFQuotientCompatible parent m → WeightedBound B m ∨
      ∃ e ∈ children, TNFQuotientCompatible e.2 m

def refineEntry (fs : List (Refinement B)) (e : Entry) : List Entry :=
  match fs.find? (fun f => tableOK e.2 f.parent) with
  | none => [e]
  | some f => f.children.map fun c => (e.1 ++ c.1,c.2)

theorem refineEntry_sound (fs : List (Refinement B)) (e : Entry)
    (m : Machine) (hm : TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ c ∈ refineEntry fs e, TNFQuotientCompatible c.2 m := by
  unfold refineEntry
  cases h : fs.find? (fun f => tableOK e.2 f.parent) with
  | none => exact Or.inr ⟨e,by simp,hm⟩
  | some f =>
    have hf : tableOK e.2 f.parent = true := @List.find?_some (Refinement B) (fun x => tableOK e.2 x.parent) f fs h
    have hp := tableOK_sound _ _ hf
    rw [hp] at hm
    rcases f.sound m hm with hb | ⟨c,hc,hq⟩
    · exact Or.inl hb
    · exact Or.inr ⟨(e.1 ++ c.1,c.2),List.mem_map.mpr ⟨c,hc,rfl⟩,hq⟩

def refineRoster (fs : List (Refinement B)) (rs : List Entry) : List Entry :=
  rs.flatMap (refineEntry fs)

theorem refineRoster_sound (fs : List (Refinement B)) (rs : List Entry)
    (m : Machine) (h : WeightedBound B m ∨ ∃ e ∈ rs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ c ∈ refineRoster fs rs, TNFQuotientCompatible c.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · rcases refineEntry_sound fs e m hq with hb | ⟨c,hc,hm⟩
    · exact Or.inl hb
    · exact Or.inr ⟨c,List.mem_flatMap.mpr ⟨e,he,hc⟩,hm⟩

def closed (p : PartialMachine)
    (h : ∀ m, TNFQuotientCompatible p m → WeightedBound B m) : Refinement B :=
  ⟨p,[],fun m hm => Or.inl (h m hm)⟩

#print axioms refineEntry_sound
#print axioms refineRoster_sound
end BB6.Agent50QuotientRefinement
