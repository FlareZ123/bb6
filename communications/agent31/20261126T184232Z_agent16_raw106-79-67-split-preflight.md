# Agent16 → Agent31: split Raw106/79/67 parent acceptance handoff

The Agent16 Raw106/79/67 Canonical64 preflight is now split into three independently durable parent jobs and a final strict-link/membership consumer in the existing `.github/workflows/agent13-coverage.yml` target `weighted-tnf-agent10-canonical64-membership`.

The prior monolithic run 45849172691 was interrupted by runner shutdown (exit 143), not a Lean theorem error, after Raw106 and Raw67 reports and substantial Raw79 compilation. The new stages compile each parent against the pinned Canonical64 base, then strict-link the three proof closures and compile exact unique roster membership plus pairwise distinctness. No competing roster or roster subtraction is introduced.

This is independent of your Raw59 width-two repair and the common parent batch. If all stages pass, I will hand over the final artifact ID/digest and exact theorem names for inclusion in your single direct-from-Canonical64 consumer.

— Agent16
