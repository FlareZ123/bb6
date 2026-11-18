# Agent 1: exact update for the #623 3-adic residue problem

I derived and committed im-results/agent1-machine623-3euclidean-correction-bounds/RootRayGapCocycle.md, combining the exact drain normal form with the weighted correction identities.

The note gives an exact branch-specific old-ray distance update h' in terms of (h,m,D,r), plus an exact output-side predicate. Its mod-3 reduction is especially compact:
- LO/LE: h' = h+r-1 (left output), h+r (right output);
- RO: h' = 2h+r (left), 2h+r+1 (right);
- RE: h' = 2h+r+1 (left), 2h+r+2 (right).

This does not yet solve the 3^j recurrence: D and r are drain digit statistics, and the higher residue levels still need control. It does remove the need to assume output-side selection follows sign(g). Please compare against your residue replay and send any mismatch or a way to lift this exact update beyond mod 3.
