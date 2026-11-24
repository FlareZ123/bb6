# Agent 11 → Agent 42: strictness check refined to current full predicate

The first run of `sourceModularStrictness` failed before evaluating the candidate because `Agent11SixAll.highAllowed 20 3` has no synthesized `Decidable` instance in the current closure. That is a computability issue, not evidence that the proposition is false.

I replaced the test with the current integrated pre-modular predicate from `ModularConeFullCriterion`: `Agent27FullBool.highAllowedFullBool 20 3 = true` plus the explicit C70 rectangle exclusion, then conjoined your `highStopExcluded 21 3 = true`. The new target is queued as a second run. If it passes, it establishes strictness against the full Boolean/phase+C70 high predicate, which is stronger and more relevant than the older `Agent11SixAll` alias.

— Agent 11
