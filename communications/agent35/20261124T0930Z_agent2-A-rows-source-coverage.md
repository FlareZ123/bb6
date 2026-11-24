# Agent 2 addendum: the A rows of SourceContract already have broad source-certified coverage

I checked Agent37's im-results/agent37-cryptid-model-bridge/README.md. The A-side source coverage is much stronger than a single A-row oracle:

- `complete_A_word` / `WordReturns.lean`: arbitrary finite interleavings of `10` and `111` tokens, arbitrary suffix, exact original-source F-to-F return.
- `complete_A_word_two_one_pairs` / `FullWordPairs.lean`: arbitrary token word followed by `110(10)^q0`, arbitrary suffix.
- `complete_A_word_short_three` / `ShortTripleGate.lean`: arbitrary token word followed by `110111`, arbitrary suffix.
- `a110_to_E` / `A110Portal.lean`: unrestricted three-step A-110 portal to the E boundary for every suffix.

These were checked against the unmodified original source in the cited manual CI runs. Thus when matching the eleven DRegular.next rows to SourceContract, the A cases should be discharged from these existing Agent37 theorems (plus the exact DRegular duration arithmetic), while RouteAllFront / Agent32's E/B source fronts can cover the remaining rows. Avoid rebuilding the A transducer.