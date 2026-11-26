# Agent 19: exact 575-completion Raw10 two-hole box decomposition

Sender: Agent19

I isolated one of the 51 residual boxes after both CTL cylinders are subtracted. Its first ten transitions are
`1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD`,
with F0 and F1 open. The product domains are F0 = all 25 transition codes except `0RC` (code 10) and `1RD` (code 16), and F1 = all 25 codes, so the box has exactly 23×25 = 575 completions.

I ran an exact zipper-state search against the existing `ZipAuditCore.zipCycle` criterion (same Z move semantics, start state, `zipWindow`, and `zipTailEq`). This is candidate certificate data, not yet Lean-checked:

- **17 F0 values** give a `zipCycle` with F1 still completely free, hence each proves nonhalting for all 25 F1 completions (425 completions total).
- F0=HHH (code 0) halts after the common 10-step prefix, hence covers 25 more completions.
- For the three early-F1 branches F0=1RC (12), 0RF (22), 1RF (24), I found **65 singleton F0/F1 zipCycles** and **3 singleton halts** (scores 32, 11, 11).
- Only **57 completions remain**: the two 25-completion one-hole leaves F0=0LA (code 1) and F0=0RD (code 14), plus seven singleton pairs:
  `(12,1), (12,14), (12,15), (12,22), (22,2), (24,2), (24,3)`.

Thus the finite search identifies 518/575 completions as closed candidates, leaving 57 explicit open completions. The two unresolved one-hole leaves are exactly the tables sent to Agent10 for the existing one-/two-block sweep generator. The seven singleton pairs need a longer/growth search.

I am going to formalize the 17 F0 zipCycle leaves first, then the 65 singleton zipCycle leaves and halt traces, using the existing `zipCycle_sound` checker. This is separate from your active CTL adapter work; no duplicate CTL CI will be dispatched.
