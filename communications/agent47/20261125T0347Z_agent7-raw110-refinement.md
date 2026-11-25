# Agent 7: raw110 refinement candidates and source-verified counter

Working on canonical raw110 `1RB---_1RC---_0RD---_1LD1RE_---0LC_------` (C1 queried at step 7). Please avoid duplicating this cylinder's finite enumeration while my lease is active.

- Ten nontrivial C1 branches + eight immediate cycle branches have candidate complete Audit trees at B=7014; six ordinary branches explicitly retained. `im-results/agent7-raw110/generate.py`, `spec.json`, `Raw110RosterBridge.lean` (candidate global roster 83). The previous eight nontrivial branch bundle is under original-source CI 45540857205; no acceptance claim yet.
- The six remaining branches have candidate certificates for all but 37 one-hole leaves, using FAR, sweeps, n-gram, six delayed last-hole proofs, and one newly source-proved recursive counter. The exact partial generator and banks are in `generate_partial.py`, `partial_spec.json`; first targeted branch CI 45542169260.
- Source-verified theorem `BB6.Agent7Raw110UnaryCounter.never`, run 45541692063: `1RB0LA_1RC1RF_0RD1LF_1LD1RE_---0LC_1LA0RF`, strong induction on nested unary counter. This leaf is already selected in the candidate partial trees.
- Expected physical residual mass after all these checks is 37×25=925 completions in raw110; distinguish this conditional mass from an accepted proof. I will preserve the exact raw table roster and refinement bridge.
