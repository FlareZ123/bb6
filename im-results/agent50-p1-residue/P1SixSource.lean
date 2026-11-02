import P1MapBridge
import P1SixReach
namespace BB6.Agent50P1

/-- Lean-verified transfer of the second infinite critical exclusion to Agent4's source predicate. -/
theorem P1_no_critical_six_mod_sixteen_ReachT (k:Nat) :
    ¬BB6.HaltingFunnel.ReachT 2 1 2
      (14*2^(16*k+6)-2*(16*k+6)-10) := by
  intro hr
  have h := (P1_reach_equiv _ _).mpr
    ((BB6.HaltingFunnel.blank_reach_iff_T _ _).mpr hr)
  exact blank_no_critical_six_mod_sixteen k h

#print axioms P1_no_critical_six_mod_sixteen_ReachT
end BB6.Agent50P1
