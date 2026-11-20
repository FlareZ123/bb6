import LassoTraceAudit
import TranslatedThreeSlotFamilies

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6Coverage
namespace ThreeSlotFamilies

/-- The exact depth-four physical audit expression used by the global
    ResidualFrontierManifest.  Keeping the expression local avoids importing
    its unrelated terminal-manifest and report machinery. -/
def familyDepth4Audit : FrontierAudit (DecidedBelow 6) emptyTable :=
  lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4

def period3P1 (x : NonAState) (right : Bool) : PartialMachine :=
  refine emptyTable a0 (act true right x.val)

def period3P2 (x : NonAState) (y : Fin 6) (right : Bool) : PartialMachine :=
  refine (period3P1 x right) (zeroSlot x.val) (act false (!right) y)

def period4P1 (x : NonAState) (right : Bool) : PartialMachine :=
  refine emptyTable a0 (act true right x.val)

def period4P2 (x : NonAState) (right : Bool) : PartialMachine :=
  refine (period4P1 x right) (zeroSlot x.val) (act false (!right) 0)

def entryOneP1 (x : NonAState) (right : Bool) : PartialMachine :=
  refine emptyTable a0 (act false right x.val)

def entryOneP2 (x : NonAState) (right : Bool) : PartialMachine :=
  refine (entryOneP1 x right) (zeroSlot x.val) (act true (!right) 0)

/-- One physical-audit branch can be transported exactly to its first
    unassigned input when the old decision oracle rejects the parent. -/
private theorem family_lasso_open_step
    (p : PartialMachine) (d : Nat) (slot : Slot)
    (hf : lassoDecisionOracle p 6 6 12 2 4 = false)
    (hs : firstUnknownPhysical p 12 finiteBlank = some slot)
    (m : Machine) :
    (lassoPhysicalTraceAudit p 6 6 12 12 2 4 (d+1)).open m ↔
      (lassoPhysicalTraceAudit (refine p slot (m slot))
        6 6 12 12 2 4 d).open m := by
  have hn : ¬ lassoDecisionOracle p 6 6 12 2 4 = true := by
    simp [hf]
  simp only [lassoPhysicalTraceAudit, dif_neg hn]
  split
  · rename_i hnone
    simp [hnone] at hs
  · rename_i actual hsome
    have heq : actual = slot := Option.some.inj (hsome.symm.trans hs)
    subst actual
    rfl

/-- The finite old-oracle and physical first-unknown checks for every
    Schema-I prefix are computed from the exact Lean definitions. -/
theorem period3_oracles :
    ∀ (x : NonAState) (y : Fin 6) (right : Bool),
      lassoDecisionOracle emptyTable 6 6 12 2 4 = false ∧
      lassoDecisionOracle (period3P1 x right) 6 6 12 2 4 = false ∧
      lassoDecisionOracle (period3P2 x y right) 6 6 12 2 4 = false ∧
      lassoDecisionOracle (period3Table x y right) 6 6 12 2 4 = false := by
  decide

theorem period3_first_unknown :
    ∀ (x : NonAState) (y : Fin 6) (right : Bool),
      firstUnknownPhysical emptyTable 12 finiteBlank = some a0 ∧
      firstUnknownPhysical (period3P1 x right) 12 finiteBlank =
        some (zeroSlot x.val) ∧
      firstUnknownPhysical (period3P2 x y right) 12 finiteBlank =
        some (oneSlot y) ∧
      firstUnknownPhysical (period3Table x y right) 12 finiteBlank = none := by
  decide

/-- Every completion of every Schema-I table is an open leaf of the old
    depth-four physical audit. -/
theorem period3_parent_open_all (x : NonAState) (y : Fin 6)
    (right : Bool) (m : Machine)
    (hm : compatible (period3Table x y right) m) :
    familyDepth4Audit.open m := by
  have hA : m a0 = act true right x.val :=
    hm a0 (act true right x.val) (by
      simp [period3Table, a0, zeroSlot, oneSlot, refine, x.property])
  have hX : m (zeroSlot x.val) = act false (!right) y :=
    hm (zeroSlot x.val) (act false (!right) y) (by
      simp [period3Table, a0, zeroSlot, oneSlot, refine, x.property])
  have hY : m (oneSlot y) = act false (!right) 0 :=
    hm (oneSlot y) (act false (!right) 0) (by
      simp [period3Table, a0, zeroSlot, oneSlot, refine, x.property])
  have ho := period3_oracles x y right
  have hu := period3_first_unknown x y right
  have h3 :
      (lassoPhysicalTraceAudit (period3Table x y right)
        6 6 12 12 2 4 1).open m := by
    simp [lassoPhysicalTraceAudit, ho.2.2.2, hu.2.2.2]
  have h2 :
      (lassoPhysicalTraceAudit (period3P2 x y right)
        6 6 12 12 2 4 2).open m := by
    apply (family_lasso_open_step (period3P2 x y right) 1
      (oneSlot y) ho.2.2.1 hu.2.2.1 m).2
    simpa [period3P2, period3Table, refine, hY] using h3
  have h1 :
      (lassoPhysicalTraceAudit (period3P1 x right)
        6 6 12 12 2 4 3).open m := by
    apply (family_lasso_open_step (period3P1 x right) 2
      (zeroSlot x.val) ho.2.1 hu.2.1 m).2
    simpa [period3P2, period3P1, refine, hX] using h2
  have h0 :
      (lassoPhysicalTraceAudit emptyTable
        6 6 12 12 2 4 4).open m := by
    apply (family_lasso_open_step emptyTable 3 a0 ho.1 hu.1 m).2
    simpa [period3P1, refine, hA] using h1
  simpa [familyDepth4Audit] using h0

/-- Exact old-oracle and first-unknown facts for all Schema-II prefixes. -/
theorem period4_oracles :
    ∀ (x : NonAState) (right : Bool),
      lassoDecisionOracle emptyTable 6 6 12 2 4 = false ∧
      lassoDecisionOracle (period4P1 x right) 6 6 12 2 4 = false ∧
      lassoDecisionOracle (period4P2 x right) 6 6 12 2 4 = false ∧
      lassoDecisionOracle (period4Table x right) 6 6 12 2 4 = false := by
  decide

theorem period4_first_unknown :
    ∀ (x : NonAState) (right : Bool),
      firstUnknownPhysical emptyTable 12 finiteBlank = some a0 ∧
      firstUnknownPhysical (period4P1 x right) 12 finiteBlank =
        some (zeroSlot x.val) ∧
      firstUnknownPhysical (period4P2 x right) 12 finiteBlank =
        some (oneSlot 0) ∧
      firstUnknownPhysical (period4Table x right) 12 finiteBlank = none := by
  decide

theorem period4_parent_open_all (x : NonAState) (right : Bool)
    (m : Machine) (hm : compatible (period4Table x right) m) :
    familyDepth4Audit.open m := by
  have hA : m a0 = act true right x.val :=
    hm a0 (act true right x.val) (by
      simp [period4Table, a0, zeroSlot, oneSlot, refine, x.property])
  have hX : m (zeroSlot x.val) = act false (!right) 0 :=
    hm (zeroSlot x.val) (act false (!right) 0) (by
      simp [period4Table, a0, zeroSlot, oneSlot, refine, x.property])
  have hA1 : m (oneSlot 0) = act false (!right) x.val :=
    hm (oneSlot 0) (act false (!right) x.val) (by
      simp [period4Table, a0, zeroSlot, oneSlot, refine, x.property])
  have ho := period4_oracles x right
  have hu := period4_first_unknown x right
  have h3 :
      (lassoPhysicalTraceAudit (period4Table x right)
        6 6 12 12 2 4 1).open m := by
    simp [lassoPhysicalTraceAudit, ho.2.2.2, hu.2.2.2]
  have h2 :
      (lassoPhysicalTraceAudit (period4P2 x right)
        6 6 12 12 2 4 2).open m := by
    apply (family_lasso_open_step (period4P2 x right) 1
      (oneSlot 0) ho.2.2.1 hu.2.2.1 m).2
    simpa [period4P2, period4Table, refine, hA1] using h3
  have h1 :
      (lassoPhysicalTraceAudit (period4P1 x right)
        6 6 12 12 2 4 3).open m := by
    apply (family_lasso_open_step (period4P1 x right) 2
      (zeroSlot x.val) ho.2.1 hu.2.1 m).2
    simpa [period4P2, period4P1, refine, hX] using h2
  have h0 :
      (lassoPhysicalTraceAudit emptyTable
        6 6 12 12 2 4 4).open m := by
    apply (family_lasso_open_step emptyTable 3 a0 ho.1 hu.1 m).2
    simpa [period4P1, refine, hA] using h1
  simpa [familyDepth4Audit] using h0

/-- Exact old-oracle and first-unknown facts for all Schema-III prefixes. -/
theorem entryOne_oracles :
    ∀ (x : NonAState) (right : Bool),
      lassoDecisionOracle emptyTable 6 6 12 2 4 = false ∧
      lassoDecisionOracle (entryOneP1 x right) 6 6 12 2 4 = false ∧
      lassoDecisionOracle (entryOneP2 x right) 6 6 12 2 4 = false ∧
      lassoDecisionOracle (entryOneTable x right) 6 6 12 2 4 = false := by
  decide

theorem entryOne_first_unknown :
    ∀ (x : NonAState) (right : Bool),
      firstUnknownPhysical emptyTable 12 finiteBlank = some a0 ∧
      firstUnknownPhysical (entryOneP1 x right) 12 finiteBlank =
        some (zeroSlot x.val) ∧
      firstUnknownPhysical (entryOneP2 x right) 12 finiteBlank =
        some (oneSlot x.val) ∧
      firstUnknownPhysical (entryOneTable x right) 12 finiteBlank = none := by
  decide

theorem entryOne_parent_open_all (x : NonAState) (right : Bool)
    (m : Machine) (hm : compatible (entryOneTable x right) m) :
    familyDepth4Audit.open m := by
  have hA : m a0 = act false right x.val :=
    hm a0 (act false right x.val) (by
      simp [entryOneTable, a0, zeroSlot, oneSlot, refine, x.property])
  have hX : m (zeroSlot x.val) = act true (!right) 0 :=
    hm (zeroSlot x.val) (act true (!right) 0) (by
      simp [entryOneTable, a0, zeroSlot, oneSlot, refine, x.property])
  have hX1 : m (oneSlot x.val) = act false right x.val :=
    hm (oneSlot x.val) (act false right x.val) (by
      simp [entryOneTable, a0, zeroSlot, oneSlot, refine, x.property])
  have ho := entryOne_oracles x right
  have hu := entryOne_first_unknown x right
  have h3 :
      (lassoPhysicalTraceAudit (entryOneTable x right)
        6 6 12 12 2 4 1).open m := by
    simp [lassoPhysicalTraceAudit, ho.2.2.2, hu.2.2.2]
  have h2 :
      (lassoPhysicalTraceAudit (entryOneP2 x right)
        6 6 12 12 2 4 2).open m := by
    apply (family_lasso_open_step (entryOneP2 x right) 1
      (oneSlot x.val) ho.2.2.1 hu.2.2.1 m).2
    simpa [entryOneP2, entryOneTable, refine, hX1] using h3
  have h1 :
      (lassoPhysicalTraceAudit (entryOneP1 x right)
        6 6 12 12 2 4 3).open m := by
    apply (family_lasso_open_step (entryOneP1 x right) 2
      (zeroSlot x.val) ho.2.1 hu.2.1 m).2
    simpa [entryOneP2, entryOneP1, refine, hX] using h2
  have h0 :
      (lassoPhysicalTraceAudit emptyTable
        6 6 12 12 2 4 4).open m := by
    apply (family_lasso_open_step emptyTable 3 a0 ho.1 hu.1 m).2
    simpa [entryOneP1, refine, hA] using h1
  simpa [familyDepth4Audit] using h0

#print axioms period3_oracles
#print axioms period3_first_unknown
#print axioms period3_parent_open_all
#print axioms period4_oracles
#print axioms period4_first_unknown
#print axioms period4_parent_open_all
#print axioms entryOne_oracles
#print axioms entryOne_first_unknown
#print axioms entryOne_parent_open_all

end ThreeSlotFamilies
end BB6Coverage
