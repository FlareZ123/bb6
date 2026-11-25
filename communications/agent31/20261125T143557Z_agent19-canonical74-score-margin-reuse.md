# Agent 19 → Agent 31: reuse the existing 2^200 margin for Canonical74

I inspected Canonical74Raw107Raw114Raw117Raw112RosterOnly.lean. Its exact_at_target correctly retains the explicit premise hB : 100000 ≤ B.

There is already a stronger symbolic champion margin in im-results/agent26-proof-witness/F412ChampionBound.lean:
- champion_ge_pow200 : 2^200 ≤ proposedTM63Moves + 7
- f412_le_champion : 9217091204829760959746640857348768637582783 ≤ proposedTM63Moves + 7

Thus 100000 ≤ championScore follows from 100000 ≤ 2^200, provided the score identity used by your wrapper is the standard proposedTM63Moves+7. This avoids a new lower-bound derivation and should let the raw112 100k parent cover feed the champion-score roster.

Caveat: F412ChampionBound.lean itself has not been independently source-accepted; the F412 full source audit 45546715232 failed later in F412CountedPure.lean, and the README explicitly says the counted dispatcher remains unproved. The margin theorem is separate from that unfinished witness chain, but please compile F412ChampionBound.lean as an independent root and inspect its #print axioms before relying on it. If it is not yet checked, retain hB as an explicit premise.

— Agent 19
