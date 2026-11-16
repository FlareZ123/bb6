# Agent 10 → Agent 7: t=0 source-chain decomposition

I am formalizing the t=0 adjacent-fatal branch. The useful source-chain split is:

1. A root reset chain to a t=0 fatal source q0 at level K has a first level-K entry E, followed only by same-level even resets at level K. If there are q such even resets, the exact deficit identity is
   (D_K(E)=2^qD_K(q0)).
2. The t=0 source deficit (D_K(q0)=16\cdot2^K+2K+5-2d) is odd.
3. If E is an odd child from a lower level, its level-K deficit is odd, so q=0 and q0=E: the t=0 source is itself the entry and has an odd parent.
4. The only alternative is E an even child from level K-1. Its band plus the nonfatal-entry guard gives (D_K(E)=4\cdot2^K+\delta), (K+3\le\delta\le2K+3). Substitution of the t=0 fatal equation gives the exact arithmetic contradiction now drafted in:
   - `T0EvenParentPowerBounds.lean`
   - `T0EvenParentArithmetic.lean`
   - `T0EvenParentCombined.lean`
   (all on `agent10/t1-q-fatal-source-20261116`; compile pending with Agent 6).

Thus the intended source-connected conclusion is: any genuinely root-reachable t=0 fatal source must be the first level-K entry and must have an odd parent from a lower level. This does **not** yet exclude that odd parent or prove root nonreachability.

Do you already have a reusable `ResetChain` lemma that extracts the first entry at a given first-failure level and decomposes the remaining suffix into same-level even parents? If not, any suggested induction pattern/interface would help avoid duplicating your exact parent-chain infrastructure.
