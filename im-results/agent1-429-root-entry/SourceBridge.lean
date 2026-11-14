import JRootEntry
import BB429PhysicalFrontier
import JPhysicalPrefix

namespace BB429RootEntry

open BB6Coverage

/-- The explicit twelve-slot table used for the root monitor is exactly
    the canonical completion of the repository's eleven-row physical
    prefix. The last slot is D/1, and both tables halt there. -/
theorem source429_eq_target429 :
    source429 = BB429PhysicalFrontier.target429 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;> cases b <;>
    decide

/-- The 35-step root endpoint is exactly the canonical physical
    J(0,0) tape, translated by its absolute head coordinate 3. -/
theorem rootTape_matches_physical_j00 (x : Int) :
    rootTape x = BB429JPhysical.jTape 0 0 (x - 3) := by
  rw [rootTape_exact_support]
  apply Bool.eq_iff_iff.mpr
  simp [BB429JPhysical.jTape, BB429JPhysical.jMark, BB429JPhysical.jHole]
  omega

theorem target429_blank_root_35 :
    run BB429PhysicalFrontier.target429 35 blank = some j00Config := by
  rw [← source429_eq_target429]
  exact blank_reaches_j00_after_35

theorem target429_root_entry_is_physical_j00 :
    run BB429PhysicalFrontier.target429 35 blank = some j00Config ∧
    (∀ x, j00Config.tape x = BB429JPhysical.jTape 0 0 (x - 3)) := by
  exact ⟨target429_blank_root_35, rootTape_matches_physical_j00⟩

/-- The complete 277-step monitored blank-root prefix transfers to the
    canonical physical table. -/
theorem target429_root_277_monitor :
    runWithHeadMax BB429PhysicalFrontier.target429 277 blank = some rootAfter277 := by
  rw [← source429_eq_target429]
  exact root_after_277_computes

theorem target429_root_277_frontier_base :
    runWithHeadMax BB429PhysicalFrontier.target429 277 blank = some rootAfter277 ∧
    rootAfter277.2 = 16 ∧ rootAfter277.1.tape 16 = true ∧
    (∀ x, 16 < x → rootAfter277.1.tape x = false) := by
  exact ⟨target429_root_277_monitor, root_after_277_head_max,
    root_after_277_mark, root_after_277_blank_right⟩

/-- The generic monitored-record C/0 frontier theorem is valid for the
    canonical physical #429 table as well. -/
theorem target429_c0_gate_advance_of_record
    (n : Nat) (c d : Config) (M F : Int)
    (hmon : runWithHeadMax BB429PhysicalFrontier.target429 n c = some (d, M))
    (hhead : d.head = M) (hF : F ≤ M)
    (hblank : ∀ x, F < x → c.tape x = false)
    (hstate : d.state = (2 : Fin 6))
    (hread : d.tape d.head = false) :
    run BB429PhysicalFrontier.target429 2 d = some (c0GateAfterTwo d) ∧
    (c0GateAfterTwo d).tape (M + 1) = true ∧
    (∀ x, M + 1 < x → (c0GateAfterTwo d).tape x = false) := by
  have hmon' : runWithHeadMax source429 n c = some (d, M) := by
    rw [source429_eq_target429]
    exact hmon
  have h := source429_c0_gate_advance_of_record n c d M F hmon'
    hhead hF hblank hstate hread
  simpa [source429_eq_target429] using h

#print axioms source429_eq_target429
#print axioms rootTape_matches_physical_j00
#print axioms target429_root_entry_is_physical_j00
#print axioms target429_blank_root_35
#print axioms target429_root_277_frontier_base
#print axioms target429_c0_gate_advance_of_record

end BB429RootEntry
