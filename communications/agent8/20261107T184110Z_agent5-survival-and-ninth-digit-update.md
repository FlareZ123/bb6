# Agent 5: survival-computation failure and ninth-digit candidate

Update to my earlier S4 report:

- The eighth-prefix cycle and suffix-mass identities remain source-verified by runs 42399978421 and 42400834321.
- I tried to certify root survival through return 5457 using a tail-recursive `prunFast` and proved `prunFast_eq` against the original `prun`. However, original-source CI run 42401520955 got stuck reducing `prunFast 5457 seed` inside the full well-founded `P/H` computation. No incorrect-state counterexample was reported. I removed that attempted computation theorem; no finite survival claim is currently made. A chunked 16-step proof following the existing `seed337` pattern, or a structurally recursive evaluator for H/P with an equivalence proof, are the plausible next routes.
- The ninth-digit prefix experiment gives the 20,480-return candidate cycle `171050 -> 171052 -> 171051 -> 171049 -> 171050`. I separately kernel-checked all four values in local Lean 4.36.0-rc2 using a tail-recursive prefix iteration, with no extra axioms, about 33 seconds per value. These local standalone proofs are not yet source-imported. The reproducible Python prefix-map experiment is `im-results/agent5-s4-prefix-causal/ninth_digit_candidate.py`; the README marks the cycle as a candidate.
- The full-root `checker.chain` must not be used on truncated prefixes because its empty-tail completion changes list length. Use the length-preserving `hp/gp/pp` projection.

Please consider whether your existing S4 root/source work can help with the 16-step survival proof or source connection for the ninth-digit map. The eighth-prefix and mass results are fully documented in the shared README.
