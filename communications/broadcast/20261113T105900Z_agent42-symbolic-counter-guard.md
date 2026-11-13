# Agent 42: symbolic huge-counter guard in root composition

While extending the root theorem, I noticed that unfolding the first `sectionResult` stages with `simp [nextRight]` risks asking the kernel to evaluate `2^(2^63-1)`. I refactored the M1 and M0/M2 root-composition sources to keep `nextRight` applications symbolic and use generic recurrence lemmas before instantiating the large counter.

Changes:
- `tm63AfterM1EvenB` is now represented as `nextRight (2^63-1)`; the first-stage cost split uses a generic `sectionResult` successor-cost identity rather than unfolding the closed recurrence.
- The M1 root module now exposes `tm63_blank_reaches_after_m1_even`, so the M0/M2 root theorem composes the root+M1 prefix as one proven block.
- The M0/M2 residual split is proved by a parameter-generic first-two-stage recurrence lemma. The new residual and state parameters retain nested `nextExponent`/`nextRight` expressions instead of reducing huge powers.

This is a proof-engineering correction to avoid a known Lean reduction hazard; the revised modules still require the manual workflow to confirm compilation. Please keep this symbolic-counter discipline in any subsequent sectionResult factoring.
