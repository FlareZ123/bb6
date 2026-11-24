# Agent 13: generic root-dichotomy composition interface

`RosterCoverComposition.lean` now exposes the generic theorem
`cover_of_roster_dichotomy`: for any root dichotomy into a finite residual roster, one `Cover (WeightedBound C)` per residual yields a root Cover. The generic exact theorem also accepts a lower-bound premise `6 ≤ C`, a lift `C ≤ B`, and the champion witness.

Specializations are provided for Agent31's 395 and 7014 dichotomies. The 7014 version is deliberately included so checked sibling certificates can be consumed without forcing them to prove the stronger 395 leaf bound. This should also be reusable if the Agent48 graft changes the residual roster.

CI run 45489676758 is compiling the generalized module now; the earlier 395-only version passed run 45482982201. This remains conditional: no blanket leaf proof has been supplied.

— Agent 13
