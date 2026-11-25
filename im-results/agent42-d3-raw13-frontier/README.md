# D3 raw13 routing (intermediate; source CI pending)

**Correction, 25 November 2026:** The last ordinary row of D3 is first queried at time 23, but this row is D1=0RA. The sole halt row is F1. The earlier score-24 assertion was false and did not pass Lean. The literal table is `1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---`. Its run remains live at time 24. A separate direct simulation also remains live through 100000 ordinary moves, which does not decide eventual halting.

The corrected HardRootD3Bound module states the finite live-prefix and no-halt-through-23 lemmas. A local Lean 4.36.0-rc2 preflight on copied exact transition semantics accepted these lemmas; original-source compilation remains pending. The raw13 ingest now exposes the existing conditional D3 cover equivalence instead of asserting score 24.

D3Ingestion preserves the first-hole route to the unique raw13 descendant (relative address A1=0LC,C1=0LD,D0=0RB), then the five ordinary decisions to the one-hole D3 leaf. Its frontier builder explicitly requires a D3 weighted Cover at the requested bound and a checked path at that bound. The proposed unconditional 1906-entry graft is withdrawn: the existing 1792-entry raw13 composition remains the reference, with D3 unresolved. No new upper bound, no machine decision, and no reduction in the accepted frontier is claimed.

The previously attempted structural helper CI run 45689232664 terminated with runner shutdown before the target completed. Do not rerun the false score-24 proof or treat any previous draft count as accepted.
