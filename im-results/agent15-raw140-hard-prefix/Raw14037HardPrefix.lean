import Raw14037ClusterEntry
import Raw14037Section
import Raw14037EREntry
import Raw140ERSuffixClosed
import Raw14037RootBridge

namespace Raw14037HardPrefix
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer
open Raw140Double (Reach)
open Raw140ERSweep Raw140ERSuffix
open Raw14037EREntry Raw140ERSuffixClosed Raw14037RootBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The first common post-entry section state for Raw140 residual 37. -/
def section13 : BState :=
  ⟨1,false,U 1 3 ++ U 3 13 ++ U 5 23,[S 2,S 1,S 5]⟩

/-- Compose the source-accepted blank entry with the generic clean section half. -/
theorem section0_to_section13 :
    run M37 1759 Raw14037ClusterEntry.section0.prim = some section13.prim := by
  simpa only [Raw14037ClusterEntry.section0, section13, U,
    List.replicate_succ, List.replicate_zero, List.cons_append,
    List.append_assoc, List.append_nil, List.nil_append] using
    (Raw14037Section.section23 M37 (fill_extends _ _) 5 (U 5 23))

theorem blank_to_section13 :
    run M37 8171 primBlank = some section13.prim := by
  simpa only [show 6412 + 1759 = 8171 by decide] using
    (join Raw14037ClusterEntry.entry37 section0_to_section13)

/-- Closed-form ER-bank arithmetic identifies the 22-bank drain endpoint with
the finite bridge state already certified independently. -/
theorem drain_endpoint :
    (boundary 4 true
      (S 1 :: (oddword (iterate 22 (bankWord 13) .t1155).1 ++ ([] : List Sym)))
      (tailWord (iterate 22 (bankWord 13) .t1155).2)) =
      Raw14037RootBridge.afterBank.prim := by
  rw [Raw140ERSuffixClosed.iterate_closed]
  decide +kernel

theorem section13_to_afterBank :
    Reach M37 section13.prim Raw14037RootBridge.afterBank.prim := by
  have h := Raw14037EREntry.drainBank 13 22 ([] : List Sym)
  rw [drain_endpoint] at h
  simpa only [section13, U, List.replicate_succ, List.replicate_zero,
    List.cons_append, List.append_assoc, List.append_nil, List.nil_append] using h

theorem blank_to_afterBank :
    Reach M37 primBlank Raw14037RootBridge.afterBank.prim := by
  exact Reach.trans ⟨8171, blank_to_section13⟩ section13_to_afterBank

theorem blank_to_transferOut :
    Reach M37 primBlank Raw14037RootBridge.transferOut.prim := by
  exact Reach.trans blank_to_afterBank
    ⟨13730 + (83 + 45*3), Raw14037RootBridge.afterBank_to_transferOut⟩

/-- Any completion preserving Raw37's assigned rows inherits the whole symbolic
prefix, so the theorem applies to the entire one-hole residual cylinder. -/
def Extends37 (M : Table) : Prop :=
  ∀ q b m, M37 q b = some m → M q b = some m

theorem step_ext37 (M : Table) (ext : Extends37 M) (c c' : Prim)
    (h : primStep M37 c = some c') : primStep M c = some c' := by
  cases hm : M37 c.q (c.r 0) with
  | none => simp [primStep, hm] at h
  | some m => simpa [primStep, hm, ext _ _ _ hm] using h

theorem run_ext37 (M : Table) (ext : Extends37 M) (n : Nat) (c c' : Prim)
    (h : run M37 n c = some c') : run M n c = some c' := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih =>
    rw [run] at h ⊢
    cases hm : primStep M37 c with
    | none => simp [hm] at h
    | some d =>
      simp only [hm, Option.bind_some] at h
      rw [step_ext37 M ext c d hm]
      exact ih d h

theorem blank_to_transferOut_ext (M : Table) (ext : Extends37 M) :
    Reach M primBlank Raw14037RootBridge.transferOut.prim := by
  obtain ⟨t, ht⟩ := blank_to_transferOut
  exact ⟨t, run_ext37 M ext t _ _ ht⟩

#print axioms section0_to_section13
#print axioms blank_to_section13
#print axioms drain_endpoint
#print axioms section13_to_afterBank
#print axioms blank_to_afterBank
#print axioms blank_to_transferOut
#print axioms step_ext37
#print axioms run_ext37
#print axioms blank_to_transferOut_ext
end Raw14037HardPrefix
