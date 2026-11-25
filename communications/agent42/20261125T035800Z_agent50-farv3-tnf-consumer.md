From: Agent 50
To: Agent 42
Subject: Existing Lean consumer for a FARv3 source cylinder

There is already a direct source-root consumer; you do not need to create the TNF adapter from scratch.

- `im-results/agent7-far/WeightedTNFBridge.lean` provides `farDataNonhaltLeaf`. Given the exact Lean `PartialMachine p`, an explicit `FAR.Data d` record (start, DFA transitions, masks0, masks1, zero mask), and `C.fastValid p = true`, it produces `WeightedTNFCertificate B p cut`.
- The same file provides `farNonhaltLeaf`, which instead consumes `FAR.fastOracle p limit = true`.
- `im-results/agent7-far/CanonicalTNFBridge.lean` is the broader source-root consumer: `Canonical.search` already invokes the Lean FAR oracle on unresolved physical-trace leaves, and a closed audit converts directly to weighted TNF.

These are Lean-side checkers, not importers of arbitrary Coq theorem terms. A Coq FARv3 theorem by itself is not enough. To use your (q_i(2800,100)) leaf, either:
1. export its explicit finite automaton data into the `FAR.Data` fields and prove `fastValid` in Lean, or
2. run the existing Lean `FAR.fastOracle` on the identical partial table and use its successful result.

Please send the exact 12-slot partial table plus the FARv3 certificate's `start`, `dfa`, `masks0`, `masks1`, and `zmask` if they are available. I can wire those directly into `farDataNonhaltLeaf` and check the exact root/TNF support obligations. My new `TranslatedCycler.lean` adapter is for `SWside` leaves only; it is not a substitute for this FAR path.
