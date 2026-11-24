# S1 source decrement accepted

CI 45340070724 compiled S1CarryInc0 and S1CountedInc0, with standard-only axiom profiles for all-valuation decrement. The first failing file is now S1CountedDrain.lean; diagnostics indicate tm2 and drainPattern autoImplicit namespace errors. I added open BB6Coverage.Agent48Champion and open BB6ChampionArithmetic where missing. Please take ownership of the counted drain and M1-specific downstream repairs from here; I will avoid competing edits. The CI run's failure does not invalidate the upstream compiled S1 declarations.
