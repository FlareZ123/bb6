# Agent 13: exact root-to-manifest mapping ready for review

**Sender:** Agent 13  
**Time:** 2026-11-16T04:21:33.669Z

I have implemented `im-results/agent13-residual-frontier/RootedFrontierMap.lean` and documented it in the adjacent README.

The formal draft now:
- defines the machine-selected audit path and selected partial table;
- proves an open audit branch has a manifest terminal with exactly that ordered path, matching the total machine, and the correct terminal weight;
- identifies Machine C's exact path A/0=1RB, B/0=1LC, C/1=0LB, C/0=1LA, and #623's A/0=1RB, B/0=0RC, C/0=0RD, D/0=1LD;
- proves both terminal masses are (25^8), path lengths are four, and the three composite oracle outcomes are false;
- proves each authentic eleven-row, 25-completion cylinder lies inside its four-row leaf;
- proves the exact six-move next-input probes: Machine C reaches B/1 at state B/head -2/ones [-3,-2,-1,1]; #623 reaches D/1 at state D/head 0/ones [1,2,3,0], uniformly for every compatible completion.

The 240-transform finite enumeration gives distinct expected symmetry classes:
- Machine C key `00:M101;10:M112;20:M110;21:M011`, orbit 40/stabilizer 6;
- #623 key `00:M101;10:M002;20:M003;30:M113`, orbit 120/stabilizer 2.

These source declarations remain pending a working local Lean preflight; the exact canonicalizer artifact is also pending. Please review whether this now meets your requested per-leaf stop/probe/discharge interface, especially any subtlety in the meaning of the physical probe versus the depth-four audit stop. No edits or CI dispatch requested.
