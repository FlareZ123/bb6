import RootNoFatalPrefix
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429RootNoFatalPhysical

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429NoFatalGuard BB429RootNoFatalPrefix

/-- The physical blank configuration is represented by the genuine
    blank source zipper. -/
theorem root_blank_represents : Represents rootBlank blank := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro j <;> simp [rootBlank, z, blank]

/-- Lift the 9,243-step guarded source run and every guarded prefix to
    the original physical #429 table on the complete bi-infinite tape.
    This is the full-tape bridge for the root certificate, not merely a
    finite-window simulation. -/
theorem root_prefix_no_fatal_physical :
    ∃ d : Config,
      BB6Coverage.run target429 9243 blank = some d ∧
      Represents rootEndpoint d ∧
      (∀ t : Nat, t ≤ 9243 →
        ∃ e : Config,
          BB6Coverage.run target429 t blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) := by
  have hsource : BB429OddExcursion.run 9243 rootBlank = some rootEndpoint :=
    runNoFatal_to_run 9243 rootBlank rootEndpoint root_prefix_no_fatal_source
  obtain ⟨d, hraw, hrep⟩ :=
    source_run_rep 9243 rootBlank blank root_blank_represents rootEndpoint hsource
  refine ⟨d, hraw, hrep, ?_⟩
  intro t ht
  obtain ⟨p, hp, hpSafe⟩ := root_prefix_all_prefixes_nonfatal t ht
  obtain ⟨e, he, hrepE⟩ :=
    source_run_rep t rootBlank blank root_blank_represents p hp
  refine ⟨e, he, ?_⟩
  intro hbad
  rcases hrepE with ⟨hstate, hcurrent, hleft, hright⟩
  have hstate' : p.state = 2 := hstate.symm.trans hbad.1
  have hcurrent' : p.current = false := hcurrent.symm.trans hbad.2.1
  have hright0 : p.right.getD 0 false = true := by
    have hr0 := hright 0
    have hr0' : e.tape (e.head+1) = p.right.getD 0 false := by
      simpa using hr0
    exact hr0'.symm.trans hbad.2.2
  have hfatal : fatalCZero p = true := by
    change (p.state == 2 && !p.current && p.right.getD 0 false) = true
    simp only [hstate', hcurrent', beq_self_eq_true, Bool.not_false, Bool.true_and]
    exact hright0
  simp [hfatal] at hpSafe

#print axioms root_blank_represents
#print axioms root_prefix_no_fatal_physical

end BB429RootNoFatalPhysical
