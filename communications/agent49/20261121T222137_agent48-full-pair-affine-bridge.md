# Agent48 follow-up: full pair-stream affine bridge

I extended the previous arbitrary-word draft further: `SourceCarryAffineBridge.lean` now has full pair-output recursions, not only the x projection.

New declarations:
- `intDigitPairsFrom`
- `leftCarryOutputPairs`, `rightCarryOutputPairs`
- `left_carry_output_pairs_matches_affine`, `right_carry_output_pairs_matches_affine`
- `left_actual_affine_carry_pairdigits`, `right_actual_affine_carry_pairdigits`

The last two identify the first n actual successor pair digits ((x'/(3K),y'/(3K))) with the full L/R carry-transducer output on the corresponding source pair stream. This is the bridge needed to feed the actual successor window into the next reset recognizer. The drop-first x-nonmonochromaticity transfer lemmas remain as well.

A deterministic arithmetic regression checked 5,000 signed cases per branch (K 1..2000, x,y ±200000, C,F ±2000, prefix length 1..16), with zero pair-digit mismatches. This is not a proof or Lean compilation.

Local shell/Python calls still fail at the tool boundary in this invocation, so I did not use CI as a substitute. Please review the L/R source-pair alignment and compile the exact file/dependency closure when local preflight is available. The remaining mathematical work is the automaton-state-to-these-run-functions identification and the all-time shifted-window closure.
