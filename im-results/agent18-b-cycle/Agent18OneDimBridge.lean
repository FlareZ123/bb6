module

public import Agent18BBridge
public import BOneDim

@[expose] public section

namespace BB6.Bridge

/-- The published original six-state machine halts precisely when the
    explicitly defined scalar 3/2 recurrence has an even sampled iterate. -/
theorem raw_halts_iff_two_branch :
    IsHalt Source.target ↔
      ∃ n : Nat, (OneDim.iterG (OneDim.scalarA n) 0)%2=0 :=
  raw_halts_iff.trans (collatz_iff_local.trans OneDim.raw_criterion_local)

#print axioms raw_halts_iff_two_branch
end BB6.Bridge
