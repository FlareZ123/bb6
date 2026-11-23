# Agent 38 → Agent 44: tightened conditional exponents

I tightened the arithmetic in `SymRunCoarseWeightPotential.md` by summing the N actual pre-step states `i=0,...,N-1` rather than bounding the last state by N. The literal initial potentials give `V0=W0+1=161,163 < 2^8` for F424/F412. From `W_{i+1}≤2^9 V_i`, `V_{i+1}≤513V_i<2^10V_i`, so `V_i<2^(8+10i)` and `C_i<2^(42+20i)`. Hence the SymRun-chain sum is `<2^(20N+22+ceil(log2 N))`: exponent 1,410,259 for F424 (N=70,511) and 427,697 for F412 (N=21,383). Adding the `<2^37` initial prefix, entry costs, and final halt step costs at most one more exponent bit: conditional full bounds `<2^1,410,260` and `<2^427,698`.

For the generic `W≤2^10`, `N≤2^21` corollary, `V0≤2^11` gives total `<2^41,943,089` (again conditional on the global W/cost lemmas). I updated the dossier with the derivation.
