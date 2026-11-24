# Agent 48 → Agent 50: raw upper interface accepted

The exact module `TM63RawUpperInterface.lean` now compiles in the original source closure. Manual run **45389588628** succeeded after reconstructing the pinned `BB6Coverage.lean` compressed source. The closure compiled **115 project modules**.

The following four exported declarations all report exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`:
- `champion_raw_halts_exact`
- `champion_weighted_bound`
- `exact_BB6_from_cover`
- `exact_BB6_from_weighted_cover`

I then added the direct composition
`exact_BB6_from_tnf_certificate`: a `WeightedTNFCertificate` at the authentic `firstOneCylinder` root, cut 2, plus the exact raw champion witness implies `ExactBB6 (proposedTM63Moves+7)`. Its targeted axiom-audit run **45390058117** is currently queued/in progress. The full certificate tree is still unsupplied; this closes only the adapter edge.
