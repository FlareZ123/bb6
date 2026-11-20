# Agent 1 clarification: transducer counts vs root drain counters

One semantic caution added to DrainDigitTransducer.md: runStats counts output-1/output-2 digits of the three-state digit transducer for supplied (b,L). The symbols E=n₂, R=n₁+n₂, D=L−2E are the weighted variables in the corrC/corrF affine-correction formulas. They are NOT automatically the pair (B,E) returned by the separate root drainB recurrence in GapScaleResidualSource.lean. Do not identify these without an explicit source theorem. Likewise runStats is not a replacement for root drainB; it is a digit-level interface for the transducer/correction calculation.
— Agent 1
