import RleCoverageGraft
import AuditRaiseBound
import Cryptids608NonHalt
import IncrementalAuditReport

namespace BB6.Agent17.F289Coverage
open BB6Coverage BB6.Cryptids608

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

def singleton (m : Machine) : PartialMachine := fun slot => some (m slot)

theorem compatible_singleton_iff (m a : Machine) :
    compatible (singleton a) m ↔ m = a := by
  constructor
  · intro h
    funext s
    exact h s (a s) rfl
  · intro h
    subst m
    intro s t ht
    exact Option.some.inj ht

theorem singleton_mass (m : Machine) : cylinderMass (singleton m) = 1 := by
  simp [cylinderMass, freeSlotCount, singleton]

theorem singleton_score_cover {m : Machine} {n B : Nat}
    (hs : HaltsAfter m n) (hb : n+1 ≤ B) :
    Cover (DecidedBelow B) (singleton m) := by
  apply Cover.leaf
  intro a ha
  rw [(compatible_singleton_iff a m).mp ha]
  exact Or.inr ⟨n, hb, hs⟩

def bound : Nat := 2^237

theorem bound_ge_six : 6 ≤ bound := by decide
theorem first_score_le : 932242535661307148726923126800831715518673957228+1 ≤ bound := by decide
theorem second_score_le : 111579188581812927653348117002306046024821208051411619955580898884568781+1 ≤ bound := by decide

noncomputable def raised : FrontierAudit (DecidedBelow bound) emptyTable :=
  cryptids608GraftedAudit.raiseBound bound_ge_six

noncomputable def withFirst : FrontierAudit (DecidedBelow bound) emptyTable :=
  addCertificate raised (singleton expectedRLE_1)
    (singleton_score_cover literal_score_1 first_score_le)

noncomputable def withBoth : FrontierAudit (DecidedBelow bound) emptyTable :=
  addCertificate withFirst (singleton expectedRLE_2)
    (singleton_score_cover literal_score_2 second_score_le)

theorem raised_open_iff (m : Machine) :
    raised.open m ↔ cryptids608GraftedAudit.open m :=
  cryptids608GraftedAudit.raiseBound_open_iff bound_ge_six m

theorem withBoth_open_iff (m : Machine) :
    withBoth.open m ↔ cryptids608GraftedAudit.open m ∧
      m ≠ expectedRLE_1 ∧ m ≠ expectedRLE_2 := by
  simp [withBoth, withFirst, addCertificate_open_iff, empty_compatible,
    compatible_singleton_iff, raised_open_iff, and_assoc]

theorem closes_first : ¬ withBoth.open expectedRLE_1 := by
  intro h
  exact ((withBoth_open_iff _).mp h).2.1 rfl

theorem closes_second : ¬ withBoth.open expectedRLE_2 := by
  intro h
  exact ((withBoth_open_iff _).mp h).2.2 rfl

theorem exhaustive (m : Machine) : DecidedBelow bound m ∨ withBoth.open m :=
  withBoth.exhaustive m (empty_compatible m)

/-- Exact transfer of two units of open mass, assuming both singleton roots
were genuinely open in the previous audit. No tree-report evaluation. -/
theorem withBoth_report_of_open
    (h1 : cryptids608GraftedAudit.open expectedRLE_1)
    (h2 : cryptids608GraftedAudit.open expectedRLE_2) :
    withBoth.report =
      (cryptids608GraftedAudit.report.1 + 2,
       cryptids608GraftedAudit.report.2 - 2) := by
  have hne : expectedRLE_2 ≠ expectedRLE_1 := by
    intro h
    have hslot : expectedRLE_2 ((0 : Fin 6), true) ≠ expectedRLE_1 ((0 : Fin 6), true) := by decide
    exact hslot (congrFun h _)
  have h1fresh : ∀ m, compatible (singleton expectedRLE_1) m → raised.open m := by
    intro m hm
    rw [(compatible_singleton_iff m _).mp hm, raised_open_iff]
    exact h1
  have h2fresh : ∀ m, compatible (singleton expectedRLE_2) m → withFirst.open m := by
    intro m hm
    rw [(compatible_singleton_iff m _).mp hm]
    change (addCertificate raised (singleton expectedRLE_1)
      (singleton_score_cover literal_score_1 first_score_le)).open expectedRLE_2
    rw [addCertificate_open_iff _ _ _ _ (empty_compatible _),
      compatible_singleton_iff, raised_open_iff]
    exact ⟨h2, hne⟩
  have hr := cryptids608GraftedAudit.raiseBound_report bound_ge_six
  have hfirst := addCertificate_global_report_of_open raised
    (singleton expectedRLE_1)
    (singleton_score_cover literal_score_1 first_score_le) h1fresh
  have hsecond := addCertificate_global_report_of_open withFirst
    (singleton expectedRLE_2)
    (singleton_score_cover literal_score_2 second_score_le) h2fresh
  change raised.report = cryptids608GraftedAudit.report at hr
  change withFirst.report = _ at hfirst
  change withBoth.report = _ at hsecond
  rw [singleton_mass] at hfirst hsecond
  rw [hr] at hfirst
  rw [hsecond, hfirst]
  congr 1 <;> omega

private theorem incompatible_A1 {p : PartialMachine} {m : Machine} {t : Transition}
    (hp : p ((0 : Fin 6), true) = some t)
    (hne : m ((0 : Fin 6), true) ≠ t) : ¬ compatible p m := by
  intro h
  exact hne (h _ _ hp)

noncomputable local instance depth4OpenDecidable (m : Machine) :
    Decidable (depth4ResidualAudit.open m) :=
  FrontierAudit.openDecidable depth4ResidualAudit m

theorem oldOpen_1 : cryptids608GraftedAudit.open expectedRLE_1 := by
  apply (cryptids608GraftedAudit_open_iff _).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact incompatible_A1 (t := expectedRLE_r1 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r2 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r3 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r4 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r5 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r6 ((0 : Fin 6), true)) rfl (by decide)

theorem oldOpen_2 : cryptids608GraftedAudit.open expectedRLE_2 := by
  apply (cryptids608GraftedAudit_open_iff _).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact incompatible_A1 (t := expectedRLE_r1 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r2 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r3 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r4 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r5 ((0 : Fin 6), true)) rfl (by decide)
  · exact incompatible_A1 (t := expectedRLE_r6 ((0 : Fin 6), true)) rfl (by decide)

theorem withBoth_report : withBoth.report =
    (cryptids608GraftedAudit.report.1 + 2, cryptids608GraftedAudit.report.2 - 2) :=
  withBoth_report_of_open oldOpen_1 oldOpen_2

#print axioms oldOpen_1
#print axioms oldOpen_2
#print axioms withBoth_report

#print axioms withBoth_open_iff
#print axioms withBoth_report_of_open
#print axioms exhaustive

end BB6.Agent17.F289Coverage
