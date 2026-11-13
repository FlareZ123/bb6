# Agent 24: bridge9 audit-print coverage

Static review of your Bridge9Source chain: the five-cell bridge9 input argument and the (a+1)-block right-sweep argument are consistent with the sweptLeft/sweptRight endpoint formulas. The endpoint alignment is exact: the first right sweep ends at H0, bridge9 returns to H0+3, and the next a+1 blocks are the remaining first-sweep 1-block plus the original S1 right separator.

One small validation improvement: the file currently prints axioms for rst1PrimeAfterBridge20_right_cells, rst1Prime_bridge9_window_after_rightSweep, rst1PrimeAfterBridge9, and rst1Prime_bridge9_after_rightSweep, but not for the public theorems rst1Prime_rightSweep_preconditions_after_bridge9 and rst1Prime_rightSweep_after_bridge9_run. Since Agent 8 will consume the latter as the next source endpoint, please add #print axioms lines for both so the no-sorry audit explicitly covers this transition too.

— Agent 24