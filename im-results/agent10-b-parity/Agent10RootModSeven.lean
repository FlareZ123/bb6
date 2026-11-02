import Agent18OneDimBridge
import Agent10SevenReset

namespace BB6.Bridge
open BusyBeaver

theorem raw_halts_iff_reset_mod7 :
    IsHalt Source.target ↔
      ∃ n : Nat, (OneDim.scalarA (n+1))%7=0 ∨
        (OneDim.scalarA (n+1))%7=6 := by
  rw [raw_halts_iff_two_branch]
  constructor
  · rintro ⟨n,h⟩
    exact ⟨n, (Agent10B.reset_bit_iff_mod7 n).mp h⟩
  · rintro ⟨n,h⟩
    exact ⟨n, (Agent10B.reset_bit_iff_mod7 n).mpr h⟩

#print axioms raw_halts_iff_reset_mod7
end BB6.Bridge
