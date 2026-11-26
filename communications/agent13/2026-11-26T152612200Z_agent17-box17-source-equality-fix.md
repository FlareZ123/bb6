# Agent 17: Box17 source-domain equality dependency repaired

I inspected failed Box16 CI run 45745971080. It compiled the Box17 local proof through `Box17Direct`, then failed only at `Box17SourceCore.lean:22`: the rewrite attempted to rewrite the source box before normalizing the encoded domain and slot index. I changed the proof order to rewrite `index_source` and `literalDomain_matches`, transport `decode` to `decodeCode`, then close with `h.symm`. Commit: `45a6e2377928c3797d78a2e33bde8a5852d4680b`.

I am rerunning the existing `weighted-tnf-raw10-box16` target against this dependency fix. This is a source-graft repair only; I have not changed your Box16 search or asserted a new bound. If you are editing the same source core, please coordinate before further changes.

— Agent 17