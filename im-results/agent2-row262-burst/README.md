# Uniform 9q primitive-step burst for BB(6) row262

**Agent 2, 2026-11-03.** Intermediate research under [R009](../../research/issues/R009.md); this is not a machine decision, a new BB(6) lower bound, or a universal six-state bound. Root: blank state A of the exact 11-defined-transition six-state RLE

`1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---`.

## Original-machine statement

Use the [Agent35 source](../agent35-row262-section/Row262.lean) of the original elementary transition table: `BB6.Row262.Cfg` contains `st, left, head, right`, with nearest tape cell first on both lists. Let `R_q = [0,0,1]^q` and `L_q = [0,1,1]^q` (bit lists, nearest-first). For *every* natural `q` and arbitrary finite binary left and right suffixes `ls,ys`:

```
run (9q) (A, ls, 0, [1,0] ++ R_q ++ ys)
      = (A, L_q ++ ls, 0, [1,0] ++ ys).
```

The original physical head advances **exactly 3q cells rightward**. For each 9-step block, state A is reached after its 5th and 9th primitive transitions. Thus the full segment cannot pass through the absorbing F/1 halt. Original-source code in [PairBurst.lean](PairBurst.lean) defines `rightBurst` and `leftBurst` and proves `burst_d5`, `burst_a4`, `pair9`, and the all-natural `pair_burst` by induction on q, using the original `run_add`. A previously completed local compilation with definition-identical shadow `Row262` produced only standard axioms `[propext, Quot.sound]` for the final theorem, with no `sorry`. The **unaltered original source**, together with Agent35's full `Row262Complete.lean`, was independently compiled and checked by the shared manual-only [row262 workflow, run 41579357743](https://github.com/FlareZ123/bb6/actions/runs/41579357743) (**SUCCESS**, 2026-11-03 04:40 UTC). Its step `Verify exact universal row262 9q burst source theorem` passed, including the raw-RLE SFT. Final theorem axiom audit: `[propext, Quot.sound]`; no `sorry`, `native_decide`, custom axioms, or altered transition definitions.

## Equivalent scalar acceleration

For the exact physically finite binary tape and head-relative coordinate `x = Σ_i tape[i] 2^(p-i)`, the source state A and the above right prefix enable two successive original A sections (D0, then A1). Their combined map is

```
F²(x) = 8x + 33/4
```

over **9** elementary transitions. Consequently, whenever q copies of the `001` right pattern follow `10`, all q pairs can be skipped in one valid operation:

```
F^(2q)(x) = 8^q x + (33/4)*(8^q - 1)/7,
raw transitions = 9q.
```

The tape identity is the primary proof; the scalar formula is a direct consequence of the [Agent35 exact scalar encoding](../agent35-row262-section/Scalar.md). It is exact for arbitrary suffixes, without any blank-origin assumption. In particular this theorem does **not** exclude the separate A0, right-11 halting gate, and an occurrence of the right prefix in a true orbit cannot prove the orbit always avoids the gate.

## Reproducibility and limitations

[The independent original-RLE SFT](test_pair_burst.py) parses all 11 transitions, constructs whole finite physical tapes, and checks complete configurations and primitive step counts for 2,688 seeded configurations with q=0..27 and arbitrary random left/right suffix bits. It executes **326,592** individual original raw transitions and tests all 5- and 9-step intermediate A checkpoints. Its observed result is `PASS`. This is useful regression evidence; the **all-q** statement is supplied by Lean induction, not sampling.

Potential next use: count q-burst lengths along authentic blank-origin A checkpoints, instrument a checker-backed jump in a genuinely rooted simulator, and seek a cross-section invariant that excludes the **separate** A0/right11 halt gate. Do not promote a raw trace extension or a synthetic-burst acceleration to an undecided-machine outcome.

**Novelty:** The all-q burst is a specialization of Agent35's existing complete A-return grammar; no claim of independent external novelty or new resolved root is made. It is preserved under `im-results/`, not `results/`.

## All-prefix halting-safety certificate

[PairBurstSafe.lean](PairBurstSafe.lean) imports the original-source 9q theorem and proves the actual frozen F/1 halting configuration is fixed by every original machine step. Its theorem `BB6.Row262.pair_burst_no_halt` states for every `q,t,ls,ys` with `0 ≤ t ≤ 9q` that **none** of the `t`-step original-source configurations inside the accelerated burst is the frozen F/1 halt. Proof: a hypothetical frozen midpoint would persist forever, contradicting the formally established final A state. The exact 9q shortcut therefore preserves original primitive-time halting semantics as well as its endpoint. The expanded original-source [manual Lean run 41580403032](https://github.com/FlareZ123/bb6/actions/runs/41580403032) **SUCCEEDED** (2026-11-03 04:51 UTC); the final theorem axiom audit is `[propext, Quot.sound]` only, no sorry.

## Blank-rooted bounded utility experiment

An independently written exact A-section simulator of the same rooted machine computed **10,000,000 actual A returns**, comprising **46,717,881 original primitive transitions**, without encountering the halting gate. A second independent bit-packed model using this theorem as a bulk jump reproduced at the 10-millionth A return the exact primitive count 46,717,881, head coordinate 2,741 and 2,722 nonblank cells. Its trace used **12,702 bulk bursts**, representing **3,292,741 pair iterations** of this theorem. This is empirical evidence of the accelerator's practical utility on the actual orbit; a finite run is no all-time nonhalting proof. The original source and Lean theorem do not depend on this experiment.
