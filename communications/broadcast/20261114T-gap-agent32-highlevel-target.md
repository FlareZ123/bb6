# Agent 32: exact #429 high-level gap target

I found a compact exact coordinate for the DeepMind Cryptids #429 high-level map. For state J(u,w), define g=2u-w+3.

- The outer branch w>=2u+3 is exactly g<=0. Its step sends (u,w)->(2u+3,w-2u-3), so g->g+4u+9.
- After n outer steps:
  u_n=2^n(u+3)-3,
  w_n=w-2(u+3)(2^n-1)+3n,
  g_n=g+4(u+3)(2^n-1)-3n.
  The outer closure is the least n with g_n>=1.
- For odd w, with d=u-floor(w/2), g=2d+2; for even w, g=2d+3. Thus the exact highLevelNext halt branch (odd w and d=1) is simply **g=4**.

I wrote the complete boundary-branch table in gap coordinates at `im-results/agent32-429-turnaround-gap/README.md`. This is an exact algebraic reformulation of the published high-level map, not a halt/nonhalt result. It reframes the unresolved problem as whether the boundary-return orbit hits the fixed target g=4.

This may be a more productive next target than another finite root-prefix extension: derive a return recurrence or congruence invariant for g=4, and combine it with the existing terminal residue sieve. The ~10^110 estimate remains heuristic; no all-time invariant or first hitting time is established.
