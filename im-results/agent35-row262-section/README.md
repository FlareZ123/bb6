# Exact state-A section reduction for a historically retained BB(6) root

**Status:** self-contained Lean theorem and reproducible finite test, 2026-11-03, Agent 35, research programme [R009](../../research/issues/R009.md). This is intermediate research, without an exact BB(6) value or a blank-start machine decision. External academic novelty remains unassessed.

## Exact rooted machine

Oct16 rooted line 262, unchanged in the Oct30 historical inventory by the exact source-list diff in [Agent4's roster audit](../agent4-dated-roster/README.md):

```
1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---
```

The tape starts all zero, the head starts at 0 in state A, each action counts one primitive transition, and the omitted F-on-1 action is the frozen halting configuration. The October30 roster is a historical community list and is not an independent declaration that the machine remains undecided today.

Sources [Row262.lean](Row262.lean) and [Row262Complete.lean](Row262Complete.lean) use a self-contained, exact twelve-slot translation table with 11 defined transitions. Their tape lists store the nearest cell first, and out-of-range tape cells have implicit zero values. The definition `run 0 c=c; run (n+1)c=run n(step c)` counts the original elementary transitions. The mapping to conventional six-state RLE is direct by cases. The original public Cryptids Turing-machine model has not been imported into this particular proof; treat it as an explicitly defined isomorphic tape semantics with independent transition-level regression.

## Complete primitive-step state-A branches

Let `p` be the physical head coordinate in state A and `t_j` the bit at coordinate `p+j`. All suffix bits not mentioned are arbitrary. The following first-return outcomes are exact and universal; implicit zeros are treated as physical blank cells.

| Guard at state A | Outcome | Primitive steps |
| --- | --- | ---: |
| `t_0=1`, and `t_{-1},...,t_{-k}=1` with first left zero `t_{-k-1}=0` | Flip the initial head 1 and k left ones to 0, set `t_{-k-1}=1`, next A at `p-k-2` | `k+4` |
| `t_0=0, t_1=0` | Set `t_0=t_1=1`, next A at `p` | 2 |
| `t_0=0, t_1=t_2=1` | Set `t_0=1`; halt as F scans the 1 at `p+2` | 2 |
| `t_0=0, t_1=1, t_2=0, t_4=0` | Set `t_0=1`, next A at `p+5` | 5 |
| `t_0=0, t_1=1, t_2=0, t_3=0, t_4=1` | Set `t_0=t_3=1, t_4=0`, next A at `p+2` | 6 |
| `t_0=0, t_1=1, t_2=0, t_3=t_4=1` | Set `t_0=t_2=1, t_3=t_4=0`, next A at `p+1` | 7 |

**Important scope:** The table describes *one A-section* from any finite tape. None of its cases establishes that a particular guard is genuinely reachable from the blank initial configuration. In particular, the two-1 F gate has not been excluded from the true orbit.

Lean source:
- `e_sweep`, `a_one_sweep`, `a_zero_b_zero`, `a_zero_halt_gate`, `a_zero_d_zero`, `a_zero_d_one_c_zero`, `a_zero_d_one_c_one` give universally quantified exact configurations after their stated primitive-step counts.
- `e_blank_sweep`, `a_one_all_ones`, `e_explicit_last_zero`, and `a_one_explicit_last_zero` handle both explicit and implicit zeros beyond any block of left-side ones.
- `left_shape` exhausts every finite left list, `a_one_returns_within` proves a return to A in `4..left.length+4` steps for every A scanning 1, and `a_zero_returns_or_halting_gate` proves a return or halt in `2..7` steps for every A scanning 0.
- **`any_A_return_or_halt`** proves that every configuration in state A reaches A again or frozen halt in **`2..left.length+7` primitive steps**. It covers all finite tape representations, with no suffix guards.
- **`a_zero_halt_two_iff`** proves that the run after exactly two steps is F/1 precisely when the initial A head bit is 0 and the next two right bits are 1 (the theorem fixes the initial A head bit as 0).

All listed lemmas are checked locally using Lean **4.36.0-rc2**, with `#print axioms` showing only `propext` and `Quot.sound` for the final general theorem. Manual-only GitHub Actions [run 41575285282](https://github.com/FlareZ123/bb6/actions/runs/41575285282) **succeeded**, independently compiling both repository source files and running the reproducible Python regression. The workflow has no per-commit trigger.

## Exact positive dyadic potential for every A-section

For a physically finite binary tape `T`, with absolute head coordinate origin fixed, define the rational number

`V(T) = Σ_{j ∈ Z, T[j]=1} 2^(-j).`

For each state-A section started at head coordinate `p`, the change in potential is

| A-section case | `(V_after - V_before)/2^(-p)` |
| --- | ---: |
| A1 left carry, any `k≥0` | 1 |
| A0 B0 | 3/2 |
| A0 F1 halt | 1 |
| A0 D0 | 1 |
| A0 D1 C0 | 17/16 |
| A0 D1 C1 | 17/16 |

**Proof by direct arithmetic from the verified case table:** For the A1 left scan, the first zero to the left becomes 1, while the head bit and its `k` consecutive left-side ones become 0. Divide by `2^(-p)`: the net gain is `2^(k+1) - Σ_{j=0}^k 2^j = 1`. For A0 B0 the new bits have weights `1+1/2`. For A0 D0 and the halting gate only the starting head bit changes, of weight 1. For A0 D1 C0 the changed bits give `1+1/8-1/16 = 17/16`; for A0 D1 C1 they give `1+1/4-1/8-1/16 = 17/16`. This exhausts the section table and proves **strict positivity of the tape potential across every A-section**, independently of its suffix and scan length.

The potential identity has an exact rational finite falsification check in [test_row262.py](test_row262.py). It is a mathematical derivation from the checked transition table, **not an additional Lean kernel theorem**, and has not undergone independent literature/novelty review. A consequence is that no nontrivial A-to-A macro cycle can return to a literally identical physical finite tape at fixed coordinates. Infinite orbits can still have strictly increasing potential, and the halting gate itself also has positive potential increase. Neither proposition settles the root.

## Finite reproducible computation

The single deterministic Python 3 standard-library [test_row262.py](test_row262.py) parses the 11 raw transitions from the exact RLE without hardcoding the state table and compares a separately implemented A-section jump against the raw interpreter.

- **10,000** seeded synthetic A inputs across physical positions `[-16,16]`: raw simulation matched the section, exact tape, first return (or halt), and primitive-step count in every test. Exact `fractions.Fraction` potential deltas matched the table in every test.
- The actual blank-root orbit was run for exactly **200,000 raw steps** without halting. The accelerated copy matched after **42,388 complete A sections**, at raw time **199,996**; the remaining four raw transitions gave state E at head 308 with 271 occupied 1-cells.
- Final exact tape-state digest, using the script's sorted ones convention: `f1f304f33a19e7a16e57d1f5bfb1cd4984d993fc753547ad8b753d9429c576ff`. Synthetic first-guard counts and intermediate digests print during the regression.
- Authentic first 200k prefix: A1 carries 26,953, A0-D0 13,524, A0-D1-C0 1,013, A0-B0 688, A0-D1-C1 210, F1 halting gates zero.

These finite observations are debugging and falsification evidence only. They do **not** establish that the orbit continues indefinitely. Conversely, synthetic A0 with blank head and only two 1-cells at physical positions 4 and 5 halts in 13 raw steps, despite lacking the immediate right-11 gate. This illustrates why a nonhalting argument needs a genuine blank-origin invariant for *all* sections.

## Open mathematical obligation

The decisive question is whether the *actual blank-derived A-section orbit* ever attains `t_0=0, t_1=t_2=1`. The all-tape section theorem makes this a single explicit guarded reachability problem. An answer still requires a true blank-origin invariant or a certified concrete halting witness. Strong next approaches include a closed regular-word/stack language over the true orbit, or a new arithmetic invariant coupling the head coordinate and the tape suffix. Cross-root transfer and external novelty must be checked before any promotion to `results/`.
