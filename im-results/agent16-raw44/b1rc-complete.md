# Raw44 B1=0RC: final C1 representative bounds and exact assembly

## Theorem

For the six-hole parent `1RB---_1RC0RC_0RD---_1LD1LB_------_------`, all 25 choices of the first unassigned transition C1 are decided by a finite weighted bound. The combined bound is 475. This settles a cylinder of 25^6 = 244,140,625 physical completions.

The two new representative child theorems, their E/F transfers, the halt proof, and the 25-way assembly theorem are kernel-checked in original-source Lean 4.36.0-rc2 using the exact previously accepted source dependencies. The assembly theorem `BB6.Agent16Raw44B1RCJoin.complete` takes five earlier source-accepted representative theorems as explicit hypotheses on their literal tables. This is a complete mathematical argument using the previous accepted results; the hypothesis-free wrapper that imports all five older generated closures simultaneously still needs its end-to-end source build. No full Raw44 or global canonical count decrement is claimed.

## New classification

| C1 | Proof | Weighted bound |
|---|---|---:|
| 1LE | finite first-hole cut + 23 AutoPump + 5 FAR residuals | 475 |
| 1LF | exact E/F permutation of 1LE | 475 |
| 1RE | finite first-hole cut + 11 AutoPump + 2 FAR residuals | 155 |
| 1RF | exact E/F permutation of 1RE | 155 |
| halt | exact first query at seven ordinary steps, all possible incoming delays bounded by 2 | 10 |

The four ordinary five-hole cylinders and the halt cylinder classify the remaining 48,828,125 complete machines in this B1=0RC parent. The earlier twenty branches are documented in [the prior result](../../results/2026-11-28-raw44-b1rc-20-c1-children-agent16.md). Their five representative bounds are 126, 373, 375, 211, 211; two E/F transfers and thirteen cycle proofs account for the rest. The checked assembly enumerates the 24 ordinary actions and the unique halt explicitly. Its transitive axioms are `propext, Classical.choice, Quot.sound`.

The new representative cuts have 40,585 and 42,193 canonical-independent physical nodes respectively. Full literal nonhalting witness tables and exact partitions are in [remaining-c1-proof.md](remaining-c1-proof.md). The local generated source `Raw44C11LECutAssembled` and `Raw44C11RECutAssembled` passed including the 24 checked child modules each. They prove `weighted_bound` at 475 and 155 respectively. Their exact source imports are reconstructed with `generate_remaining_c1.py`; `shard_audits.py` divides the larger kernel checks into smaller reductions without altering their proof semantics.

The final conditional assembly source is [Raw44B1RCComplete.lean](Raw44B1RCComplete.lean); the proposed simultaneous old-module adapter is [Raw44B1RCClosed.lean](Raw44B1RCClosed.lean). The latter remains a source integration target, not a claimed compiled theorem. The exact parent-to-top-child equality has already passed the kernel.

Note that first-one normalization permits nontrivial incoming zero-prefix delays from other states even with A0 fixed to a one-writing transition. All claims here use the existing `WeightedBound` predicate including the complete finite delay set, not an assumption that this delay is zero.
