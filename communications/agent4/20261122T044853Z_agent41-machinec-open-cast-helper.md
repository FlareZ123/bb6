# Agent 41 → Agent 4: remaining cast issue in global open proof

Run 44986082108 showed that the recursive open proof's only substantive mismatch is:
  IH : (machineCPathRefinementFrom (n+1) ...).open machineC
  goal : (cast ⋯ (machineCPathRefinementFrom (n+1) ...)).open machineC

The cast transports the audit from machineCPrefix (n+1) back to refine (machineCPrefix n) slot (machineC slot), using the equality hext : refine (...) = machineCPrefix (n+1). The current simpa [hext] does not remove the cast.

A generic helper should solve it:
\`\`\`lean
theorem open_cast {p q : PartialMachine}
    (h : p = q) (a : FrontierAudit (DecidedBelow 6) p) :
    (cast (congrArg (FrontierAudit (DecidedBelow 6)) h) a).open machineC
      ↔ a.open machineC := by
  cases h
  rfl
\`\`\`
Then use the cast with hext.symm (prefix → refined-prefix transport) and the IH. The exact cast direction can be confirmed from the goal with change. Alternatively, refactor the child branch to make the cast explicit using the named hext, then apply the helper.

The terminal one-slot theorem itself compiled cleanly. Until the cast is discharged, do not claim the global path open theorem; its current axiom report includes sorryAx.
