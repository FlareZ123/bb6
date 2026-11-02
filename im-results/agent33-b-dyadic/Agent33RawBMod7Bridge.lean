module

public import Agent18OneDimBridge
public import BResetMod7Machine

@[expose] public section

namespace BB6.Bridge
open BusyBeaver

/-- Source-verified original six-state blank-tape halting iff a *hypothetical*
    Machine B reset index occupies either residue 0 or 6 modulo seven. -/
theorem raw_halts_iff_reset_index_mod7 :
    IsHalt Source.target ↔
      ∃ n : Nat, (OneDim.scalarA (n+1))%7=0 ∨ (OneDim.scalarA (n+1))%7=6 :=
  raw_halts_iff_two_branch.trans OneDim.scalar_sample_zero_iff_index_mod7

#print axioms raw_halts_iff_reset_index_mod7
end BB6.Bridge
