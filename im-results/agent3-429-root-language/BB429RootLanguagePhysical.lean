import BB429RootLanguageCast
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429RootLanguagePhysical
open BB6Coverage BB429PhysicalFrontier BB429OddExcursion

/-- A quantified prepared C/0 configuration on the genuine original
    bi-infinite tape, with finite left word 1011101^(2m) and blank right,
    reaches the fatal C/01 gate. -/
theorem prepared_C0_fatal (m : Nat) (c : Config)
    (hrep : BB429PhysicalBridge.Represents
      ⟨2,[true,false,true,true,true,false] ++ Frontier429.ones2 m ++ [false],false,[]⟩ c) :
    ∃ c', BB6Coverage.run target429 (46+8*m) c = some c' ∧
      c'.state.val=2 ∧ c'.tape c'.head=false ∧ c'.tape (c'.head+1)=true := by
  obtain ⟨c',hr,hrep'⟩ := BB429PhysicalBridge.source_run_rep _ _ _
    hrep _ (BB429RootLanguageCast.original_zipper_fatal m)
  rcases hrep' with ⟨hs,hcur,_,hright⟩
  refine ⟨c',hr,hs,hcur,?_⟩
  exact hright 0

/-- The exact original physical machine encounters its undefined D/1 row
    two further primitive queries after the fatal C/01 configuration. -/
theorem prepared_C0_halts (m : Nat) (c : Config)
    (hrep : BB429PhysicalBridge.Represents
      ⟨2,[true,false,true,true,true,false] ++ Frontier429.ones2 m ++ [false],false,[]⟩ c) :
    BB6Coverage.run target429 (48+8*m) c = none := by
  obtain ⟨c',hr,hs,h0,h1⟩ := prepared_C0_fatal m c hrep
  have hstop := BB429PhysicalBridge.fatal_event_stops_after_two_queries c' hs h0 h1
  have ht : 48+8*m = (46+8*m)+1+1 := by omega
  rw [ht]
  change (((BB6Coverage.run target429 (46+8*m) c).bind (rawStep target429)).bind
    (rawStep target429)) = none
  rw [hr]
  exact hstop

#print axioms prepared_C0_fatal
#print axioms prepared_C0_halts
end BB429RootLanguagePhysical
