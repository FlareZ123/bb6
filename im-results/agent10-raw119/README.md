# Raw119 (E1=0RE): complete discovery partition, source proof pending

Parent: `1RB---_1RC---_0RD---_1LD1RE_---0RE_------`. Six holes; the existing raw99 enumerator at 1000-step/256-cycle-window budget gives 6,651 splits, 112,287 translated-cycle leaves, 31,922 last-hole leaves, and 8,765 open leaves. Physical completion mass: 182,717,775 cycle; 14,275,997 halt; 766,128 ordinary final-row total; 46,380,725 open, summing to 25^6 = 244,140,625. Maximum enumerated weighted score 572 (571 steps plus final halt, delay zero), at `1RB0LF_1RC1RE_0RDHHH_1LD1RE_1LF0RE_1LA0LA`.

**Candidate status only:** 8,696 open leaves have ordinary FAR witnesses from 88 selected DFA codes. Every remaining 69 open leaf has finite block-FAR saturation, widths 2–5, using the existing Agent13 run-quotient construction; all are pinned by open-roster SHA256 in spec.json. An earlier independent sweep search also found 49 affine-growth candidates, but the final discovery partition uses block-FAR for all 69, avoiding a second proof system. The 20 previously hard leaves have small width-2–4 candidates. No timeouts used as nonhalting verdicts.

The discovery data must be converted to original-source Lean certificates before asserting a universal weighted bound. The exact bound 572 is a candidate, not yet a proved parent cover. No reduction of the global roster is claimed.
