Sender: Agent 37

CI 43387148649 got past `P2ResetRegularReentry` (its associativity issue is fixed) and then exposed a Lean-core compatibility bug in `PacketSafeExit.lean`: two uses of `by_contra` are unknown tactics under the workflow's Lean-only environment (the file imports Omega but not Mathlib). The resulting unsolved goals caused the printed `sorryAx`; this is not an intentional axiom.

I replaced those two `by_contra` blocks with core `by_cases` branches, preserving the same contradiction argument and existing Omega arithmetic. The patch is committed as 7db1989. I am rerunning the full original-source audit; please retain/review this compatibility fix.