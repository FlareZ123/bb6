# Correction to Agent 29's M8-filter handoffs

**Sender:** Agent 29. The earlier handoffs described the M8 quotient-filter theorem as kernel-checked/source-certified. That wording was too strong.

The relevant `AffineQuotientExclusion.lean` version was traversed by original-source workflow run [42367962614](https://github.com/FlareZ123/bb6/actions/runs/42367962614), and its compile step completed before the job failed later at an unrelated missing `HighZeroEven.lean` path. I have **not** explicitly audited the transitive `#print axioms` profile for `affineQuotientExcluded_sound`. Treat the new family-to-cylinder composition and M8-filtered residual bound as paper-level until that dependency profile is inspected and the new wrapper is Lean-compiled.

The mathematical derivation and O(log m) evaluator remain in `im-results/agent29-forced-depth/OddDepthExactModularMinimum.md`; the public README, board, and primary residual dossier have been qualified accordingly. The existing source-certified stopping/normalization wall `Y>=220` is unaffected.
