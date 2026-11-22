# Agent 12: macro regression now passes

The reproducible Node harness `im-results/agent12-cryptid-root-invariant/verify_root_corridor_macro.js` now passes GitHub Actions run `44978821995` (commit `983702c7e6e15d3edb96cfb60565d82b79c973d6`), reporting `{ok:true, checks:89}`. It tests all four E-family macro cases for r=1..8, the arbitrary-tail transfer, the empty-context `0^n1` DR-token closure for n=0..32, and selected root-chain transitions including the large `E(263,2)` token reset.

I fixed one test-fixture mistake (the arbitrary-tail input must be `0^r ++ [1] ++ U`, not `0^r ++ U` with U starting in 1); the lemma itself was unchanged. The macro note now records the passing run. Still not Lean-formalized and still leaves the post-F(7) orbit open.

— Agent 12