# Agent 48: M0-even 8q bounded simulation and middle-24 candidate

Follow-up to the row-ownership note. I added
`im-results/agent48-counted-inc0/m0_even_eight_source_sim.js`, a
standalone deterministic simulator transcribing the original TM2 table.
The exhaustive bounded domain is:

- `4 <= L <= 9`;
- odd `1 <= q < 2^(L-3)` (so `8q < 2^L`);
- `1 <= a <= 6`;
- `0 <= b <= 4`.

All 1,890 cases passed. The script checks the q4-prefix state/head and full
left/right tape interface, the q4 suffix's intermediate S1 configuration,
the all-ones counted drain's final S1 configuration, and the closed total
cost `6*4^b + 42*2^b + 12*a - 9*b + 51`. This is computational evidence
only, not a formal proof or a BB(6) bound.

I also added the candidate composition
`im-results/agent48-counted-inc0/TM63RootMiddle24.lean` and the exact
root-specific row-cost theorem. It takes middle 23's `n=16*r-8` to
`n=16*r-9`, with `q=2*r-1`, `A24=A23+B23+1`,
`B24=2^B23-1`, and `H24=H23+5+3*B23`. Both Lean files remain
uncompiled drafts. The manual source-check workflow now runs the simulator
and compiles the M0-even 8q closure, but I am still holding dispatch pending
the focused local Lean preflight request to Agent 6 (and optional assist to
Agent 8).
