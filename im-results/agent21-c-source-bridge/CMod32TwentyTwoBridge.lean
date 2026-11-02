import CMod128SixBridge
import CMod32TwentyTwo
import Lean.Elab.Tactic.Omega

namespace BB6.CMod32TwentyTwoBridge

/-- Exact halting-gateway criterion for original Machine C, excluding
    both new symbolic infinite reset families. -/
theorem raw_halts_iff_new_modular_gates :
    BusyBeaver.IsHalt BB6.CSourceBridge.Source.target ↔
      ((∃ j:Nat, 1 ≤ j ∧ j%4 ≠ 1 ∧ j%8 ≠ 4 ∧ j%32 ≠ 16 ∧
          j%128 ≠ 6 ∧ j%32 ≠ 22 ∧
          BB6CLine.Reach (2*j+1,3*j+4,0)) ∨
       (∃ n:Nat, 1 ≤ n ∧ BB6CLine.Reach (0,4*n,24*n+23))) := by
  rw [BB6.CMod128SixBridge.raw_halts_iff_mod128_gates]
  constructor
  · rintro (⟨j,h1,h4,h8,h32,h128,hr⟩|hs)
    · have h22 : j%32≠22 := by
        intro hj
        have ht : j=32*(j/32)+22 := by omega
        have he : (2*j+1,3*j+4,0)=(64*(j/32)+45,96*(j/32)+70,0) := by
          simp only [Prod.mk.injEq]
          constructor
          · omega
          · exact ⟨by omega, trivial⟩
        exact BB6.CMod32TwentyTwo.reset_mod32_twentytwo_unreachable (j/32) (he ▸ hr)
      exact Or.inl ⟨j,h1,h4,h8,h32,h128,h22,hr⟩
    · exact Or.inr hs
  · rintro (⟨j,h1,h4,h8,h32,h128,h22,hr⟩|hs)
    · exact Or.inl ⟨j,h1,h4,h8,h32,h128,hr⟩
    · exact Or.inr hs

#print axioms raw_halts_iff_new_modular_gates

end BB6.CMod32TwentyTwoBridge
