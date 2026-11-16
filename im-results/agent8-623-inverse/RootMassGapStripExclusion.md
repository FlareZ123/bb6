# Root-mass gaps exclude a bounded n=10 far-cancellation strip

**Status:** new intermediate root-specific exclusion; Lean source draft pending focused compilation and transitive axiom audit. This is stronger than excluding three named synthetic states, but it covers only the far-terminal branches and a bounded scale interval.

## Exact root mass gap

The source section run has exact checkpoints:
- step 39: `D(79788,133932)`;
- step 40: `D(54138,239399)`;
- step 41: `D(185262,162438)`.

The source theorem `next_strict_mass` says every successful section transition increases total mass by at least 7. Iterating it in `RootExclusion.lean` proves that every genuine blank-root visit `D(a,d)` satisfies
```
a+d <= 213720
or (a,d) = (54138,239399)
or a+d >= 347700.
```
This is an exact all-time exclusion of the open mass gaps around the three checkpoints, not a finite orbit scan.

## Far/far and far/near cancellation strips at n=10

For the n=10 canonical scale band, the smaller coordinate is at least
`3^9-3 = 19680`. Restrict it to the subinterval
`19680 <= m <= 24802`.

In either far-terminal cancellation branch, the terminal ratio-four window and the preceding root-ray bridge give
`|u-13v| <= B+e+c`
(or the symmetric `|v-13u| <= B+e+c`). The uniform n=10 bounds used by the current bridge are
`B <= 145`, `e <= 306`, and `c <= 9`, hence
`B+e+c <= 460`.

Therefore, in the far/far orientation,
[
14m-460 \le u+v \le 14m+460.
]
For `19680 <= m <= 24802`, this gives
[
275060 \le u+v \le 347688,
]
strictly inside the forbidden mass interval `(213720,347700)`. The symmetric far/near orientation has the same total-mass bound. The exceptional step-40 state is also impossible because its scale coordinate is 239399, outside the interval.

The new Lean draft
`RootMassGapStripExclusion.lean` formalizes both implications:
- `far_far_n10_root_strip_unreachable`;
- `far_near_n10_root_strip_unreachable`.

It assumes the exact root visit and the terminal-window/root-ray bridge inequalities, and derives False. It does not assume a simulator trace.

## Independent finite candidate search

Agent 48's `scan_terminal_budget_family.js` independently transcribes the pinned recurrence with BigInt arithmetic. On its stated bounded domain (odd `d` from 19681 through 24819 and even offsets from -455 through 445), it finds 10,763 exact three-step halting candidates across 2,550 values of `d`. Their predecessor masses range from 275691 through 347691, and all have `d<239399`. The general source-root lemma `root_mass_corridor_excludes_small_d` in Agent 48's `RootExclusion.lean` therefore excludes every candidate in that finite search domain.

This is a useful computational cross-check, not a proof that the bounded search domain exhausts all n=10 terminal candidates. The analytic theorem in this directory covers a separate sufficient substrip without enumerating source transitions.

## Scope and next step

This removes a whole bounded portion of the two far-terminal predecessor-budget strips from the genuine blank-root orbit. It does **not** exclude the remainder of those strips, either near-terminal/gate strip, or all n>=11. In particular, it is not a #623 nonhalting proof.

The near-terminal branches have a different mass scale: `u+v` is approximately `(11/4)m`, giving about 54k–68k on the same n=10 scale interval. A useful next step is to obtain exact consecutive root checkpoints around that mass range and apply the same monotone-mass gap argument if a sufficiently wide interval exists.

All source-dependent claims still require a focused Lean compile of `RootExclusion.lean` and `RootMassGapStripExclusion.lean`, followed by `#print axioms` inspection. Keep this in `im-results/`.
