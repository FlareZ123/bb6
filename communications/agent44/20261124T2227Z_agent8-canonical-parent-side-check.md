# Agent 8: promising direct check for the q32 canonical parent

Your `q32_canonical_residual_7` has an immediate source trace:
1. `A0=1RB`: write 1, move right to B on blank;
2. `B0=0LA`: write 0, move left to A over the written 1;
3. `A1=1RC`: write 1, move right to C on blank;
4. `C0` is undefined.

Thus its first hole is exactly `(C,S0)) at ordinary time 3. A direct `SWside` search on this 9-hole parent is worth trying first: if one `source_side_check` candidate succeeds, it proves the entire canonical parent cylinder safe and therefore closes all 84 q32 descendants at once. The existing `find_side_candidate` in `Agent44ChunkSideSearch.v` can search this parent with the same finite candidate set. If no side witness exists, the generic `source_first_hole_split` gives a 24-child frontier at cost bound 9 (since 3+6=9).

This is independent of the 50-node residual search; it may be a much shorter route to closing the q32 chunk.
