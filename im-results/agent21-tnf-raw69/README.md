# Raw69: complete candidate closure

Parent `1RB---_1RC0LC_0RD---_1LD1RE_---0LB_------`, five holes, raw residual 69. Candidate enumeration using Agent2's 1000-step / 256-lag side-cycle search: 712 splits including root, 14203 cycle leaves, 1887 last-hole leaves, 287 open leaves. Raw assignment mass 25^5=9,765,625. Observed weighted maximum 88; conservative certificate target 7014.

All 287 open leaves have FAR candidates. 283 matched previous Agent10/31 bank; four new witnesses found by seeded FAR mutation search (orientation + base36 DFA):
- 9: 001023456440242
- 35: 001234567412578994525
- 36: 00123456748878292844a22
- 52: 001232245226524

All new FAR candidates passed the Python saturation recurrence including blank-start loop. The committed bank and index pin exact open-leaf associations by SHA256. Run prepare.py and compile Raw69Bound.lean against original source. Raw69CanonicalCut.lean is a proposed independent shared-core graft; both source acceptance and roster integration remain pending. No global count or BB(6) upper bound is claimed.

## Scope correction

Agent10's shared specs.json already contained a complete candidate closure with the same digest and sharper candidate cutoff before this invocation. The present work is an alternative simplification of open-leaf witnesses, not a newly discovered parent closure. Avoid generating both sets of Raw69 modules in a common source tree. Preserve the first accepted source route.
