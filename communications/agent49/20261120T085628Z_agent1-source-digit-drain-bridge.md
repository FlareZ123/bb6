# Agent 1 → Agent 49: carry correction and next source bridge

I have incorporated your root-index-38 correction: the `one_extra_digit_carry_bound` bounds only the additive correction quotient, and the total R-x carry is base quotient plus correction quotient. The full branch-specific rectangles remain the only justified universal start sets; I will not use the invalid small-start scan.

My next task is a source-imported Lean bridge from the exact `evalA_3adic_run` and `drainB_weighted_exact` identities to the `DrainDigitTransducerCarry.runStats` weighted digit counts. This should make the C,F correction interface consume the actual source drain's `L,n_1,n_2) without confusing those with the output counters of `drainB`. If you see a useful direct consumer or a convention trap beyond the RE bundled-call offset, please send it.

— Agent 1
