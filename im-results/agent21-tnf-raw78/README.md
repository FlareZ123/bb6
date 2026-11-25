# Raw78: complete candidate closure

Parent `1RB---_1RC0RE_0RD---_1LD1RE_---0LB_------`, five holes, raw residual 78. Candidate enumeration using Agent2's 1000-step / 256-lag side-cycle search: 860 splits including root, 16423 cycle leaves, 2955 last-hole leaves, 403 open leaves. Raw assignment mass 25^5=9,765,625. Observed weighted maximum 183; conservative certificate target 7014.

402 FAR candidates, including two new mutation-search hits at 158 (10123445464714464) and 297 (001234563777778777977). Last open leaf 156, `1RB1LB_1RC0RE_0RD1RA_1LD1RE_1LF0LB_0LA---`, has an exact symbolic sweep candidate. Entry 111 at state A, empty left and right 0 followed by 10 ones. Family right 0 1^(10+12n), empty left; returns to n+1 after 473+372n steps. The discovery used the insertion cut at the end of the initial right list and a 12-one opaque block. The generator replays the symbolic local equations against arbitrary tails rather than trusting the concrete trace.

All new FAR candidates passed the Python saturation recurrence including blank-start loop. The committed bank and index pin exact open-leaf associations by SHA256. Run prepare.py and compile Raw78Bound.lean against original source. Raw78CanonicalCut.lean is a proposed independent shared-core graft; both source acceptance and roster integration remain pending. No global count or BB(6) upper bound is claimed.

## Scope correction

Agent10's shared specs.json already contained a complete candidate closure with the same digest and sharper candidate cutoff before this invocation. The present work is an alternative simplification of open-leaf witnesses, not a newly discovered parent closure. Avoid generating both sets of Raw78 modules in a common source tree. Preserve the first accepted source route.
