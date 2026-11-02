import CMod128EighteenBridge
import CMod128SeventyTwo
import Lean.Elab.Tactic.Omega

namespace BB6.CMod128SeventyTwoBridge

theorem raw_halts_iff_three_new_mod128_gates :
    BusyBeaver.IsHalt BB6.CSourceBridge.Source.target ↔
      ((∃ j:Nat, 1 ≤ j ∧ j%4 ≠ 1 ∧ j%8 ≠ 4 ∧ j%32 ≠ 16 ∧
          j%128 ≠ 6 ∧ j%32 ≠ 22 ∧ j%128 ≠ 18 ∧ j%128 ≠ 72 ∧
          BB6CLine.Reach (2*j+1,3*j+4,0)) ∨
       (∃ n:Nat, 1 ≤ n ∧ BB6CLine.Reach (0,4*n,24*n+23))) := by
  rw [BB6.CMod128EighteenBridge.raw_halts_iff_mod128_eighteen_gates]
  constructor
  · rintro (⟨j,h1,h4,h8,h32,h128,h22,h18,hr⟩|hs)
    · have h72 : j%128 ≠ 72 := by
        intro hj
        have ht : j=128*(j/128)+72 := by omega
        have he : (2*j+1,3*j+4,0)=(256*(j/128)+145,384*(j/128)+220,0) := by
          simp only [Prod.mk.injEq]
          constructor
          · omega
          · exact ⟨by omega, trivial⟩
        exact BB6.CMod128SeventyTwo.reset_mod128_seventytwo_unreachable (j/128) (he ▸ hr)
      exact Or.inl ⟨j,h1,h4,h8,h32,h128,h22,h18,h72,hr⟩
    · exact Or.inr hs
  · rintro (⟨j,h1,h4,h8,h32,h128,h22,h18,h72,hr⟩|hs)
    · exact Or.inl ⟨j,h1,h4,h8,h32,h128,h22,h18,hr⟩
    · exact Or.inr hs

#print axioms raw_halts_iff_three_new_mod128_gates

end BB6.CMod128SeventyTwoBridge
