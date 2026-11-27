import Raw56RootConsumer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

def p : PartialMachine := refine BB6.Agent1Raw56Root.parent (4,true) (some ⟨false,true,2⟩)
def rd : PartialMachine := refine p (2,true) (some ⟨true,true,3⟩)

theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem support : TNFSupport p 5 := supportOK_sound _ _ (by decide)

def tree : PartialAudit := .split 7 (2,true) (byPartialMove [
  .unresolved, .unresolved, .closed (.cycle 9 1 false 1), .closed (.cycle 8 1 false 0),
  .unresolved, .unresolved, .unresolved, .unresolved, .closed (.cycle 11 1 false 5), .unresolved,
  .unresolved, .unresolved, .unresolved, .unresolved, .unresolved, .closed (.cycle 8 1 false 0),
  .unresolved, .unresolved, .unresolved, .unresolved, .closed (.cycle 2 8 true 0), .unresolved,
  .unresolved, .unresolved])

theorem checked : canonicalCheck 7014 p 5 tree = true := by decide
def remaining19 := canonicalResiduals p 5 tree
theorem count19 : remaining19.length = 19 := by decide

theorem sound19 : ∀ m, TNFQuotientCompatible p m →
    WeightedBound 7014 m ∨ ∃ e ∈ remaining19, TNFQuotientCompatible e.2 m :=
  canonicalSound 7014 p 5 tree (by decide) support root nohalt checked

def remaining18 := remaining19.filter (fun e => !sameTable e.2 rd)
theorem count18 : remaining18.length = 18 := by decide

theorem sound18 (hRD : ∀ m, TNFQuotientCompatible rd m → WeightedBound 7014 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 7014 m ∨ ∃ e ∈ remaining18, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound19 m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 rd = true
    · have heq : e.2 = rd := sameTable_sound hmatch
      exact Or.inl (hRD m (heq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms sound19
#print axioms sound18
end BB6.Agent1Raw56E1RC
