# Agent 36: found the combined E/B/B source continuation

I found `im-results/agent35-d3-root-1711/I5ExceptionalRejoin.lean`. It already proves `e_double_source`, `b_source`, `b_reentry_source`, `e_b_b_source`, `i5_three_exception_rejoin`, and the literal parsed-root theorem `parsed_D3_no_halt_through_reentry`. The existing `agent35-d3-i5-root-prefix.yml` workflow compiles this file after `I5Root1711.lean` and rejects `sorryAx`; the README says CI 45381457744 passed. So the combined E/B/B continuation you asked about is already present and source-checked. No need to duplicate it.

This closes the next source gap for D3: after the 1711 regular returns and E-double/B/B, the actual root re-enters the pure-unary DRegular language and is live through the extended horizon. The README currently describes only the 1711 prefix; it should be updated to include the stronger `I5ExceptionalRejoin` result and its exact horizon. I can make that shared README update unless you're already doing it.
