# Raw44 / B1=0RC / C1=0RE: the four formerly unresolved residuals

**Status: original-source Lean accepted.** The four exceptional residuals and the complete 27,265-node first-hole partition are assembled into `Cover (WeightedBound 211) parent` for this five-hole C1=0RE child; [assembly CI 46107082911](https://github.com/FlareZ123/bb6/actions/runs/46107082911) succeeded. This is not the full Raw44 parent.

The fixed partial machine is

```
1RB---_1RC0RC_0RD0RE_1LD1LB_------_------
```

Run `node discover.cjs '{"second":"0RE"}'` in this directory. Exact enumeration returns 27,265 decision-tree nodes: 1,136 splits, 3,225 last-hole leaves, 22,686 translated-cycle leaves, 214 sparse n-gram leaves, and precisely four hard leaves. The maximum first-hole query occurs at raw step 205. Weighted mass accounting in the canonical 25-choice first-one convention is:

| Leaf type | Number of raw total completions represented |
| --- | ---: |
| Query split whose missing row may be a halt | 819,200 |
| Translated cycles | 8,853,150 |
| Sparse n-gram closures | 11,950 |
| Last missing row queried (24 ordinary completions, one halt choice) | 80,625 |
| Four nonhalting growth candidates below | 700 |
| **Total** | **9,765,625 = 25⁵** |

The 700 residual completions are not finite cutoffs: they are handled by mathematically quantified positive-cost returns from the **actual blank start**. The recurrence modules were first developed and locally compiled against a fixture reproducing the exact `Z0`, `run0`, `sweepL` and `sweepR` interfaces. All four then passed original-source Lean 4.36.0-rc2 compilation and the axiom gate: M7 [46104882632](https://github.com/FlareZ123/bb6/actions/runs/46104882632), M4 [46105172131](https://github.com/FlareZ123/bb6/actions/runs/46105172131), M6 [46105351870](https://github.com/FlareZ123/bb6/actions/runs/46105351870), M5 [46105492096](https://github.com/FlareZ123/bb6/actions/runs/46105492096).

| Identifier | Exact partial table; remaining hole(s) | Blank entry | Return-section family and exact cost | Locally compiled Lean |
| --- | --- | ---: | --- | --- |
| M4 | `1RB0LE_1RC0RC_0RD0RE_1LD1LB_1LF1LC_1LA---`; F1 | 29 | E0, left blank, right `0 1^(4n+4)`; `n→n+1` in `40n+61` | [M4](Raw44B1RC_C1RE_M4Growth.lean) |
| M5 | `1RB1LF_1RC0RC_0RD0RE_1LD1LB_0LA1LE_---0LA`; F0 | 49 | E0, left `0011`, right `(10)^(2n+2)1`; `n→n+1` in `12n+41` | [M5](Raw44B1RC_C1RE_M5Growth.lean) |
| M6 | `1RB1LF_1RC0RC_0RD0RE_1LD1LB_0LA1LE_---0RE`; F0 | 18 | E0, left `0`, right `(10)^(2n+1)1`; `n→n+1` in `16n+35` | [M6](Raw44B1RC_C1RE_M6Growth.lean) |
| M7 | `1RB---_1RC0RC_0RD0RE_1LD1LB_---0RF_0RD1RD`; A1,E0 | 63 | B0, left blank, right `1^(3n+11)`; `n→n+1` in `8n+33` | [M7](Raw44B1RC_C1RE_TwoHoleGrowth.lean) |

The `Z0` left word **includes the head**, while its right word excludes the head; the section rows above follow that convention. The M4 proof splits into right sweep `20n+30` and left sweep `20n+31`; its eight finite arbitrary-tail rewrites are all reflexive reductions of `run0`. M5 splits into forward `8n+12`, reset and `A1↔F1` sweep `4n+29`. M6 splits into forward `8n+8`, reset and E0 return `8n+27`. M7 uses one B0–C1 entry, `n` 5-step C1 packets, a 3-step C1–E1–F0 terminal, `3n+4` D0 retreat steps, and one D1 exit.

At each proof's entry the native partial table reaches the indicated family from the blank start without querying an undefined row. The positive-cost return lemma `never_of_growth` then proves `NeverHalts m` **for every compatible completed machine**. Their disjoint physical mass is `25 + 25 + 25 + 625 = 700`. The finite-classifier mass and these all-depth proofs together give a **conditional** five-hole weighted maximum no greater than 211, but a real source-level five-hole `Cover` still requires replaying/checking all 27,265 finite tree nodes and 214 n-gram certificates, and combining the four `.proven` leaves. Do not report 211 as a kernel-accepted upper bound yet.

The full generated finite tree, all 214 n-gram certificates, translated-cycle checks and four symbolic residuals passed the assembled original-source gate in [CI 46107082911](https://github.com/FlareZ123/bb6/actions/runs/46107082911). The resulting theorem is `BB6.Agent16Raw44Cut.weighted_bound`, yielding `Cover (WeightedBound 211) parent`. This is a five-hole child, not the full Raw44 parent.
