import Raw56RootConsumer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

def p : PartialMachine := refine BB6.Agent1Raw56Root.parent (4,true) (some ⟨false,false,4⟩)
def rb : PartialMachine := refine p (4,false) (some ⟨false,true,1⟩)
def rc : PartialMachine := refine p (4,false) (some ⟨false,true,2⟩)

theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem support : TNFSupport p 5 := supportOK_sound _ _ (by decide)

def tree : PartialAudit := .split 7 (4,false) (byPartialMove [
  .unresolved, .unresolved, .closed (.cycle 9 1 false (-1)), .closed (.cycle 8 1 false (-2)),
  .closed (.cycle 7 1 false (-1)), .unresolved, .unresolved, .unresolved,
  .unresolved, .closed (.cycle 8 1 false 0), .closed (.cycle 16 1 true 2), .unresolved,
  .unresolved, .unresolved, .closed (.cycle 7 3 false (-1)), .closed (.cycle 8 1 false (-2)),
  .closed (.cycle 7 1 false (-1)), .unresolved, .unresolved, .unresolved,
  .unresolved, .closed (.cycle 5 6 false 1), .closed (.cycle 34 1 true (-4)), .unresolved])

theorem checked : canonicalCheck 7014 p 5 tree = true := by decide
def remaining14 := canonicalResiduals p 5 tree
theorem count14 : remaining14.length = 14 := by decide

theorem sound14 : ∀ m, TNFQuotientCompatible p m →
    WeightedBound 7014 m ∨ ∃ e ∈ remaining14, TNFQuotientCompatible e.2 m :=
  canonicalSound 7014 p 5 tree (by decide) support root nohalt checked

def remaining12 := remaining14.filter (fun e => !(sameTable e.2 rb || sameTable e.2 rc))
theorem count12 : remaining12.length = 12 := by decide

theorem sound12 (hRB : ∀ m, TNFQuotientCompatible rb m → WeightedBound 7014 m)
    (hRC : ∀ m, TNFQuotientCompatible rc m → WeightedBound 7014 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 7014 m ∨ ∃ e ∈ remaining12, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound14 m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 rb = true
    · have heq : e.2 = rb := sameTable_sound hmatch
      exact Or.inl (hRB m (heq ▸ hq))
    · by_cases hmatch' : sameTable e.2 rc = true
      · have heq : e.2 = rc := sameTable_sound hmatch'
        exact Or.inl (hRC m (heq ▸ hq))
      · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch,hmatch']⟩,hq⟩

#print axioms sound14
#print axioms sound12
end BB6.Agent1Raw56E1LE
