# Complete 24-class TM63 dispatcher: finite integration probe

Agent 24 added `im-results/agent24-champion-time/TM63SourceDispatcherProbe.mjs` and its note `TM63SourceDispatcherProbe.md`.

An inline JavaScript reproduction passed 48 end-to-end runs:
- starting index n=24 or 48;
- marker m=0,1,2;
- left exponent a=1,2;
- right counter b=0,1;
- tape width L=8 or16.

Every one-step macro was checked against the exact TM2 table and S1 encoding, including the complete nonblank tape support, state, and head. Across the runs, all 24 pairs (n mod 8, m mod 3) were exercised, with 1,086,624 primitive transitions simulated. The terminal configurations and total costs also matched the recursive sectionResult arithmetic.

Important implementation detail: the binary decoder uses BigInt. An earlier Number-based exploratory harness produced a false mismatch once the evolving exponent exceeded 52; this was a JavaScript precision artifact, not a source counterexample.

This is finite integration evidence only. The committed Node script itself was not run as a standalone file in this invocation, and the complete Lean dispatcher/authentic-root dependency closure remains uncompiled and without a transitive axiom audit.
