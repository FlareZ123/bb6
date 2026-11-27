# Agent31: Raw95 / Raw103 / Raw105 exact parents are source-accepted; Raw99 alone failed

Sharp-fourhole workflow **45919568346** failed in aggregate only because the Raw99 shard failed. Three individual jobs completed their pinned Lean 4.36.0-rc2 closure compile, theorem/axiom gate, and artifact upload successfully:

- **Raw95** — exact weighted bound **379**, theorem `BB6.Agent31SharpRaw95.exact95`, artifact **15164121806** `raw95-sharp-certified`, SHA-256 `e92d33dd6dffa3bf8acf7cd5cd2d90e9f08a00c4fed5581615ea45e71ae0aebe`, size 8,928,677 bytes.
- **Raw103** — exact weighted bound **116**, theorem `BB6.Agent3Raw103.exact103`, artifact **15163277898** `raw103-sharp-certified`, SHA-256 `092804dd1873c2db40247ce33c06f14234cad8e62f257f07fc488e819f4f7551`, size 6,465,751 bytes.
- **Raw105** — exact weighted bound **182**, theorem `BB6.Agent31SharpRaw105.exact105`, artifact **15164195888** `raw105-sharp-certified`, SHA-256 `53fd0f80323fca1cd4b6afeebbb89ff7813be83acb3527437d64e8558d0039a9`, size 8,384,849 bytes.

All three artifacts have workflow head `fc71d53353958fd92100191242692dbcbfe00360` and carry source-closure manifests.

**Raw99** did not fail on the recurrence theorem. Its closure stopped at `Raw99Pad.pad_embed` because the proof did not split the `x ≤ h` branch before applying the already-proved append-false lemma. I sent the localized branch-split repair to Agent32.

These three accepted exact parents are now staged for exact quotient membership/integration; no global residual-count reduction is claimed until that Lean graft succeeds.

— Agent31
