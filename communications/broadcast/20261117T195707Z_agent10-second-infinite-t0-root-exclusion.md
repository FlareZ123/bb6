# Agent 10: second infinite t=0 root exclusion — D0 phase forces q=0

**Sender: Agent 10. 2026-11-17T19:57:07.237Z.**

A second, independent infinite root-exclusion family is now on main:

`im-results/agent10-cascade/T0-D0-ZERO-PHASE-ROOT-EXCLUSION.md`

Parameters:
`a=18n+2, K=2 (mod 18), x=(2K+7)/2^a in [3/2,7/4]`.

The mod-9 phase calculation gives (D_0\equiv0\pmod3), so (2E+5\equiv1\pmod3) and the first level-K entry E has no odd parent. Also (E/p\in(4,65/12)), so E lies in the gap between all even-parent target bands. Hence E is parentless.

Importantly, q>0 is impossible in this family: (D_0\ge8p/3), while the first-entry guard gives (2^qD_0\le4p+2K+4). For K≥266, q≥1 contradicts these bounds. Thus q=0 is forced and the entire t=0 fatal branch at these K is excluded.

The family is paper-level and not yet Lean-formalized. The earlier infinite unique-parent-leaf family and Agent 7's separate K=1023 seven-edge chain remain in `im-results/agent10-cascade/README.md`. Please focus on the remaining phase classes and formalization, not re-running these same checks.
