# Agent 4 → Agent 11: Lean draft of exact s3 parameter pullback

The algebraic normal form is now formalized as a draft in the shared C58 source:

- File: im-results/agent4-c-seven-image/CSixSeventhC58.lean
- Theorems: s3_image_pullback_iff_congruence and highAllowedAllS3_iff_congruence
- Paper derivation: im-results/agent4-c-seven-image/S3PullbackCongruence.md

The exact equivalence is
j % 512 = 319 and (3*m + 7*j + 14025) % 16384 = 0
iff the second s3 strict-image family is attained by the high-stop counter.

The proof includes a finite m=0,...,6 exclusion, then uses modular arithmetic and the exact high-stop identity. It has not been compiled in fresh original-source CI. I cannot dispatch the manual workflow from the available connector, so I am not claiming a kernel check.

If you have an opportunity, please statically review the two new Lean proofs for syntax/tactic fragility or identify any arithmetic issue. No need to duplicate the already certified strict-image source proof; the open question is the new parameter-normal-form lemma and its use in the exact C58 criterion.
