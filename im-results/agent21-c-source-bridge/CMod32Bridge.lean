import CStrongBridge
import CMod32
import Lean.Elab.Tactic.Omega

namespace BB6.CMod32Bridge

/-- The original blank-tape machine's halting criterion, strengthened by
    eliminating a previously surviving infinite reset residue class. -/
theorem raw_halts_iff_mod32_gates :
    BusyBeaver.IsHalt BB6.CSourceBridge.Source.target ↔
      ((∃ j:Nat, 1 ≤ j ∧ j%4≠1 ∧ j%8≠4 ∧ j%32≠16 ∧
          BB6CLine.Reach (2*j+1,3*j+4,0)) ∨
       (∃ n:Nat, 1 ≤ n ∧ BB6CLine.Reach (0,4*n,24*n+23))) := by
  rw [BB6.CStrongBridge.raw_halts_iff_mod8_gates]
  constructor
  · rintro (⟨j,h1,h4,h8,hr⟩|hs)
    · have h32 : j%32≠16 := by
        intro hj
        have ht : j = 32*(j/32)+16 := by omega
        have heq : (2*j+1,3*j+4,0)=(64*(j/32)+33,96*(j/32)+52,0) := by
          simp only [Prod.mk.injEq]
          constructor
          · omega
          · exact ⟨by omega, trivial⟩
        exact BB6.CMod32.reset_mod32_sixteen_unreachable (j/32) (heq ▸ hr)
      exact Or.inl ⟨j,h1,h4,h8,h32,hr⟩
    · exact Or.inr hs
  · rintro (⟨j,h1,h4,h8,h32,hr⟩|hs)
    · exact Or.inl ⟨j,h1,h4,h8,hr⟩
    · exact Or.inr hs

#print axioms raw_halts_iff_mod32_gates
end BB6.CMod32Bridge
