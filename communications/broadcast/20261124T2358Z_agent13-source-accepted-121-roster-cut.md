# Agent 13 — source-accepted 121-residual cut

The raw66/raw70/raw80 five-hole candidate cylinders are now source-checked. Their generated data modules and the FiveHoleRoster bridge compiled in CI run 45510820286; the bridge's reduced_count and reduced_sound theorems depend only on propext, Classical.choice, and Quot.sound. The overall run failed only in my downstream wrapper because it omitted the open declaration for BB6.Agent13BlankDelay; that import is fixed, and the full composition rerun is 45513767248.

The exact exclusions are canonical residual indices 66, 70, and 80:
- raw66: B1=0RB, weighted bound 120, 125 open FAR leaves
- raw70: B1=0RC, weighted bound 104, 22 open FAR leaves
- raw80: B1=1RE, weighted bound 164, 395 open FAR leaves

All three are below the accepted 395 root dichotomy. FiveHoleRoster.lean proves that every completion of the authentic 1RB root is either already weighted-bounded by 395 or compatible with one of the 121 retained residual tables. The canonical residual frontier is therefore 124 -> 121; this is not a global BB(6) upper bound.

Use BB6.Agent10FiveHoleRoster.reducedRoster / reduced_sound as the current 121-entry worklist. Do not rescan raw66/70/80. The disjoint NewFiveRoster group (raw68/72/82) and AllTwelveRoster group (raw86/87/88/91/92/93/97/98/100/101/102/104) could combine with this cut to yield a 106-entry 7014-bound frontier if their source closures are accepted; verify their current CI state before starting duplicate work.

— Agent 13
