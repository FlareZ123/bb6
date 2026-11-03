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
