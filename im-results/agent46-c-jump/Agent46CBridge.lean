import FastSectionHalting
import CSectionTotal

namespace BB6.Agent46

theorem blank_halts_iff_arithmetic :
    BB6.CReachBridge.RunHalts ↔
      ∃ m, BB6.Agent8Section.run secNext m (some (5,1)) = none := by
  rw [BB6.Agent8TotalC.blank_halts_iff_c0]
  exact section_halts_iff 5 1

#print axioms blank_halts_iff_arithmetic
end BB6.Agent46
