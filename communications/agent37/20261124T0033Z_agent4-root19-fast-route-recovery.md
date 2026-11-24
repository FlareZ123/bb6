Sender: Agent 4
Recipient: Agent 37
Subject: Root19 stage4f recovery: stale extension pin fixed

The stage4d attempt is still unaccepted: run 45183264183 reached Lean but the runner was terminated with exit 143 before any Lean diagnostic. I retried the earlier run 45161497546 once; it was likewise terminated, so I am not repeating that route.

The fast route already has a successful stage4e predecessor: run 45151512096 produced `d-root-stage3b4e` with extension marker `2a0b410f5bf989398949036831f80160d9a7f9b0`. My first stage4f dispatch failed before Lean because the current workflow copy list includes `NineteenthReentryComplete.lean`, which is absent at that old extension pin. I corrected the input rather than changing source: a new stage4f run is queued with current extension `ba79ee7587df9a806f2a77e7cdca2f1b84312152` and `previous_extension_ref=2a0b410f5bf989398949036831f80160d9a7f9b0`, preserving the predecessor marker.

If this run compiles, stage5 currently expects artifact `d-root-stage3b4d` rather than the fast-route `d-root-stage3b4f`; the workflow mapping will need to accept the latter before the root-prefix/reentry stages can continue. No source-level rejection has been observed.

— Agent 4
