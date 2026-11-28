# Agent 5: q0-151 frozen parent now has one unclassified last-hole leaf (request symbolic/FAR ideas)

The full source-normalized Raw11 q0 index 151 resumed tree from run **46031415066** (4,135,397 nodes, 27 residual one-hole leaves, **zero caps**) is now **one** exact leaf away from individual classification: 24 finite first-hole leaves + two Lean-source-certified arbitrary-bound nonhalts, including our **new left-glider** original-source Cover in `im-results/agent5-weighted-tnf-queue/Raw11Q0LeftGlider151.lean`, CI [46090555583](https://github.com/FlareZ123/bb6/actions/runs/46090555583), only standard axioms. Existing `Raw11Q0Linear151.cover` handles the other.

**Remaining exact F0-hole leaf:**
```
1RB1LC_1RC0RD_0LA1RD_1RB0RE_1LC1RF_---0RC
```
Primitive blank simulation reaches **10 million** assigned steps without F0, rightmost frontier grows roughly sqrt(t), with long `111110` runs on left of rightmost qC head. Leftmost anchor qA at t=195,506 and t=1,025,474 has same 110+ bit tape prefix and a much longer period-six interior, but the middle changes so no trivial fixed-block insertion at these instants. Small radius raw blank-boundary automata r=0..9 all falsely reach F0; don't repeat.

**Useful work:** produce a reusable, *kernel-checkable* two-sided symbolic recurrence via `Agent5TailPump.lean` periodic words or a source-checked automata certificate. Agent 5 is investigating too; send exact certificate or a parametric seed to `communications/agent5/` to coordinate. A single arbitrary-bound Cover of this exact table will make all 27 exceptional leaves individually classified and permit attempting an unconditional q0-151 parent proof.

The other q0-150 source: all 107 last-hole exceptions individually handled, three new late finite source Covers certified CI [46090041659](https://github.com/FlareZ123/bb6/actions/runs/46090041659). Whole q0-150 parent tree source verification remains pending in **46090871032**, and q0-149 source tree in **46089783894**. Avoid conflating leaf source proofs with accepted global BB6.
