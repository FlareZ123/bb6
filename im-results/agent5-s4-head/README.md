# S4: all-depth blank-seed phase restrictions and two residual hazard sectors

**Research state (6 November 2026): strong quantified results in a source-mirrored accelerated model; the original S4 root decision is open.** [Full formulas, eight-module proof order, raw tables and chronological notes](FULL_RESEARCH_LOG.md).

## Exact modeled reduction

The S4 root is `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`, with modeled high-level blank seed `C(3,[0])`. After a proved finite prefix, `S4.actual_pair_cycle` gives the leading two stack digits at every surviving reduced step as an **eight-phase cycle**. Six phases are safe for arbitrary deeper tails.

The theorem `S4.blank_halts_iff_two_exceptional_gates` in [S4Hazard.lean.xz.b64](S4Hazard.lean.xz.b64) reduces **model blank halting** to two residual phase/tail families: at `n%8=4`, leading pair `(80,150)`; at `n%8=7`, leading pair `(82,231)`. These are necessary possible failure sites, not witnessed halts. Each reduced step models 32 high-level steps after the certified prefix. Earlier phase restrictions and odd/even affine updates underpin the biconditional.

The eight encoded Lean files were locally kernel checked with Lean 4.36.0-rc2 and only standard axioms; this dossier's proof historically used a copied source-shaped acceleration. A separately maintained [S4 original-source bridge dossier](../agent5-s4-source-bridge/README.md) records the authentic upstream source check, including [successful CI 41669051558](https://github.com/FlareZ123/bb6/actions/runs/41669051558). Reuse the corresponding theorem only with its actual checked imports and scope.

## Remaining problem

Prove the two exceptional deep-stack families absent from the true blank orbit under original source semantics, or construct a genuine halt. A phase restriction alone does not bound run time or settle BB(6). Detailed phase tables, hashes, reproducibility and counterexamples remain in the [full research log](FULL_RESEARCH_LOG.md).
