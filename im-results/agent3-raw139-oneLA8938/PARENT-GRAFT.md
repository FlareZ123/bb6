# Exact parent graft, no repeated enumeration

Run `python graft_oneLA.py partition.json spec-compact.json ../agent48-raw139-e0-1la/extension.json.zlib.b64 OUTDIR` against the two JSON inputs in Agent48 artifact 15147749188, discovery run 45884008735.

Tested against the actual artifact on 2026-11-27. The 45 missing open indices are exactly the 45 extension roots; all 333 extension entries consumed, every 24-way refinement checked by literal table, every original open leaf checked against its actual tree path, every new open slot assigned exactly once. The resulting tree has 40,782 split, 604,206 cycle, 247,725 last, 70,322 FAR and 15,734 open-but-covered leaves, hence 937,987 ordinary leaves (1+23*40782). Weighted bound remains 881057. New open leaves include 16 external never theorems (12 wide, long cycle, 3 growth); others preserve original candidate certs. This is an input to package6.py, **not** an accepted parent cover. The Lean audit still must check each recipe and imported theorem, including pending 8938 and the other wide/cycle proofs.

Output SHA256 (compact JSON + newline):
- partition.json e6debaf6d01e5b06bce2404a750899954fec2072f82b2b41634ac61c35ae540f
- spec-compact.json 0b1d01399e25c52e7413f6bd11e5e9dd7ce899c2e740f14efc9f8520ed54d0ef

No base or extension search required. Agent48 owns source generation/acceptance. `external_imports` lists all relevant emitted modules; use source roots or accepted .oleans with exact same Lean version. The long 11147 cycle uses chunked external theorem rather than huge monolithic reduction. The 8938 adapter is Sweep8938Bridge.lean here. Pending leaf proof CI run 45919575611.
