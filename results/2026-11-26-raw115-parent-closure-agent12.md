# Raw115: full original-source weighted parent Cover

**Status:** accepted local cylinder theorem; not yet integrated in the shared Canonical64 theorem.

The exact partial transition table is

```
1RB---_1RC---_0RD---_1LD1RE_---0RD_------
```

This is canonical-124 raw residual index 115 (canonical index 80), reached by the first-one path B0=1RC, C0=0RD, D0=1LD, D1=1RE, E1=0RD. The six unspecified entries represent 25^6 = 244,140,625 physical completions, including halt choices. The theorem does not rely on the untrusted candidate enumeration being exhaustive.

The original-source Lean theorem, from generated `Raw115Data.lean`, is

```lean
theorem all_completions (m : Machine) (hm : compatible parent m) :
    WeightedBound 7014 m
```

in namespace `BB6.Agent47Raw115`. The underlying `partialCheck` root has `residuals.length = 0`; the accepted proof composes cycle, halt, last-hole, FAR, sparse n-gram and explicit symbolic counter-return certificates. WeightedBound includes the existing first-write normalization's incoming blank-delay and final halt-query conventions. It asserts that every halting completion has weighted score at most 7014; nonhalting completions are allowed.

The 54 independently compiled branch cuts were combined without regenerating search results. The original producer run 45755928881 passed generation, preflight and 53 branch jobs. The successful repair job 139703735919 in run 45758827627 supplied the last six child roots. Its unrelated uploaded modified Sparse7 source files caused the old assembly's manifest failure; the actual child proof depends on Sparse8. The strict assembly-only repair uses original generated sources, 55 pinned artifact digests, exact successful producer jobs, byte-identical duplicate objects and each producer's exact recursive import closure. The resulting proof uses only propext, Classical.choice and Quot.sound.

- [Accepted original-source assembly run 45783903926](https://github.com/FlareZ123/bb6/actions/runs/45783903926), job 139785772479.
- Original proof source revision: `496465aee626aaf2237367fb90888499692dc772`; assembly revision: `9416c1292e50f47c06ae29ae4f6d2c80620e1755`.
- [Proof artifact raw115-certified-root, ID 15100255568](https://github.com/FlareZ123/bb6/actions/runs/45783903926/artifacts/15100255568), SHA-256 `a4eea4fe3327e993aa402544af9991e03faa56e9f04b3609a41e7f9ee615b453`, 512 exact source modules, 54 complete producer cuts.
- [Source dossier and mathematical certificates](../im-results/agent47-raw115-cut/README.md); [recovery driver](../im-results/agent12-raw115-consumer/recover_raw115.py); [immutable producer pins](../im-results/agent12-raw115-consumer/recovery-pins.json).

The bound 7014 is below the common weighted floor 6,766,859, so this local theorem can discharge Raw115's parent obligation if its exact unique membership in the accepted Canonical64 roster and the common parent-list composition pass. The narrow [membership/Cover contract](../im-results/agent12-raw115-consumer/Raw115Canonical64Membership.lean) is supplied for that audit. No new global roster number is asserted; the shared integrated remainder remains Canonical64 until Agent31's combined consumer is accepted. No BB(6) exact value is established.
