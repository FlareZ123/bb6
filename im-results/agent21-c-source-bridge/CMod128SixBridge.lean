import CMod32Bridge
import CMod128Six
import Lean.Elab.Tactic.Omega

namespace BB6.CMod128SixBridge

/-- Source-machine halting criterion after excluding another complete
    infinite reset class: j congruent to 6 modulo 128. -/
theorem raw_halts_iff_mod128_gates :
    BusyBeaver.IsHalt BB6.CSourceBridge.Source.target ↔
      ((∃ j:Nat, 1 ≤ j ∧ j%4 ≠ 1 ∧ j%8 ≠ 4 ∧ j%32 ≠ 16 ∧ j%128 ≠ 6 ∧
          BB6CLine.Reach (2*j+1,3*j+4,0)) ∨
       (∃ n:Nat, 1 ≤ n ∧ BB6CLine.Reach (0,4*n,24*n+23))) := by
  rw [BB6.CMod32Bridge.raw_halts_iff_mod32_gates]
  constructor
  · rintro (⟨j,h1,h4,h8,h32,hr⟩|hs)
    · have h128 : j%128≠6 := by
        intro hj
        have ht : j=128*(j/128)+6 := by omega
        have he : (2*j+1,3*j+4,0)=(256*(j/128)+13,384*(j/128)+22,0) := by
          simp only [Prod.mk.injEq]
          constructor
          · omega
          · exact ⟨by omega, trivial⟩
        exact BB6.CMod128Six.reset_mod128_six_unreachable (j/128) (he ▸ hr)
      exact Or.inl ⟨j,h1,h4,h8,h32,h128,hr⟩
    · exact Or.inr hs
  · rintro (⟨j,h1,h4,h8,h32,h128,hr⟩|hs)
    · exact Or.inl ⟨j,h1,h4,h8,h32,hr⟩
    · exact Or.inr hs

#print axioms raw_halts_iff_mod128_gates

end BB6.CMod128SixBridge
