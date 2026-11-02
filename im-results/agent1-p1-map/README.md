# Agent 1: P1 counter-drain exploration (2026-11-02)

**Status: intermediate investigation only.** No new BB(6) halting/nonhalting decision or bound is claimed. This material belongs under `im-results/`, not `results/`.

Target 6-state, 2-symbol machine:
`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.

Primary source (formal acceleration and its Turing-machine correctness proof):
https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean

## Independent cross-check

The raw single-step simulator parses the 12 machine instructions directly from the six-state RLE string and begins at state A, position 0, on an all-zero tape. For every hub configuration `P1(a,c) = 0∞ 1^a A> 1^c 0∞`, it independently runs until the next P1 hub and compares its coordinates with the published accelerated map. It found exact agreement on **100 successive hub-to-hub transitions, encompassing 112,669 raw Turing-machine steps**. The first transition, from P1(0,0) to P1(2,1), took 6 raw steps. An attempt to extend the naive raw simulation to 1,000 hubs exceeded a 120-second local command timeout, so no claim is made for that run.

A separate simulation of the published accelerated map from P1(2,1) ran for 1,000,000 accelerated transitions without entering its halting gate. That is **computational evidence with no universal nonhalting implication**. It reached coordinates (1,376,716, 621,355), both measured exactly in Python integer arithmetic. At accelerated transition 45 the second coordinate first becomes positive and even; the naive proposed invariant "c always odd or zero" is therefore false.

## Kernel-checked conditional structure

A self-contained Lean 4 file `GParity.lean` defines the published nested recursion G and accelerated map T. Its four theorems were checked using Lean 4.36.0-rc2:

- `G_first_even`: all G outputs have even first coordinate.
- `G_preserves_odd_second`: G maps odd second coordinates to odd second coordinates.
- `T_none_iff`: T immediately halts exactly when the input second coordinate is 2 and the first is odd.
- `T_danger_predecessor`: an odd-first-coordinate, second-coordinate-2 output from T can only originate at a predecessor with even first coordinate and second coordinate 4.

The Lean axiom printout showed only standard Lean axioms `propext`, `Quot.sound`, and for the last theorem `Classical.choice`. No `sorryAx` was present after the successful final check. The Lean arithmetic proof checks the independently restated map, while the cited DeepMind formalization establishes correspondence with the original Turing machine. In isolation this local proof does not prove its own bridge to TM semantics.

## Next problem

Analyze reachability of the set `{P1(a,4) | a even}` from initial P1(2,1). The existing kernel-certified acceleration reduces the original halting question to dynamics on natural-number pairs. The gate lemmas are elementary and may already be implicit in the published work; no novelty is asserted. Attempt invariants, return-map renormalization and exact symbolic cover proofs. Use independent validation to avoid being misled by long numerical trajectories.

## Rigorous infinite family of *synthetic* halting P1 configurations (added 2026-11-02)

Let `T(a,c)` be the accelerated map copied from DeepMind's certified reduction. For each natural `n` define

```
H(a,0) = 4
H(a,n+1) = a+10 + H(2a+12,n).
```

**Kernel-verified theorem**: for every even `a` and every `n`, `T` iterated for `2n` successful transitions from `(a,H(a,n))` reaches `(b,4)` with even `b`; the next transition reaches `(b+3,2)`, and the next application halts. The exact arithmetic identity is

```
H(a,n) + 2*n = (a+12)*(2^n-1) + 4.
H(2,n) = 14*2^n - 2*n - 10.
```

The decisive branch is a two-step affine transformation for any even `a` with `c >= a+10`:

```
(a,c) --> (a+3,c-2) --> (2*a+12,c-a-10).
```

Both transformations and the inductive halting/exact-step statements are proved in `Packet.lean`, importing `GParity.lean`. Local Lean 4.36.0-rc2 check passed. This is a mathematical theorem about *nonblank initial hub configurations*, assuming the source's established machine-to-map correspondence. It is not evidence that the blank-tape orbit (which reaches `P1(2,1)`) halts. It does not improve the known BB(6) bound, decide the target holdout, or prove a new current holdout status. Prior-art and independent proof review are requested in `communications/broadcast/2026-11-02T0130Z_agent1-p1-halting-family-review.md`.

Independent raw Turing-machine checks using `halting_family.py` initialized the **full specified synthetic tape** and confirmed termination for n=0..7:

| n | right-counter H(2,n) | defined TM transitions before undefined rule | 1s at halt |
| - | -: | -: | -: |
| 0 | 4 | 27 | 5 |
| 1 | 16 | 179 | 12 |
| 2 | 42 | 877 | 26 |
| 3 | 96 | 3843 | 54 |
| 4 | 206 | 16049 | 110 |
| 5 | 428 | 65551 | 222 |
| 6 | 874 | 264909 | 446 |
| 7 | 1768 | 1065035 | 894 |

The raw-transition count excludes an attempt to execute the undefined halt rule. Macro transition count is different and has its own explicit statement in the Lean proof.

## Separate negative controls and structural census

A full-holdout snapshot of 663 distinct, dated representative RLE strings is mirrored under `resources/`. A finite structural screen grouped them into 435 transition-table families when the starting state was forgotten, including 145 families with multiple listed starts. Retaining the distinguished initial state leaves all 663 distinct. The 435 figure does not reduce the undecided blank-tape questions: equivalent transition tables may run differently from distinct starting states.

A search of the 373 starts belonging to non-singleton transition-table families to 100,000 raw transitions each found **no verified same-tape, same-state cross-start coincidence up to translation**. An earlier 32-bit double polynomial hash collision was falsified by an exact tape comparison; the corrected screen used bases 5 and 7 and checked any candidate by replaying and comparing every nonzero tape cell. These are only bounded observations and do not establish non-coalescence. All 663 holdouts passed a separate 10,000-step screen without reaching a halt or translated cycle; this too is expected from prior decidability filtering and not new mathematics.

## Exact raw-step cost model for the synthetic halting family

The machine-level DeepMind source (rules 3, 4, 6, 10, 11) documents raw transition costs. Summing them yields the following conditional-on-the-source-rule-counts derivation for the large-counter two-step map. Write even `a=2m`. The first `P1` transition costs `4m+6`. The next odd `P1` transition costs `4m+16` and enters `P2` with initial small counter 2 and countdown `m+1`. The `m+1` repeated `P2` rule-11 sweeps cost `sum_{j=0}^m (14+8j)=4m^2+18m+14`; rule 10 exits to `P1` with cost `8m+22`. Their sum is

```
large_counter_pair_raw_steps(a) = a*a + 17*a + 58.
```

At the last gate `P1(a,4)`, the even rule takes `2a+6` raw steps and the terminal odd rule takes `2a+13`, giving `4a+19` defined transitions before the first undefined transition. Therefore for `a_j=14*2^j-12` and `H_2(n)=14*2^n-2n-10`:

```
rawDefinedSteps(n)
  = sum_{j=0}^{n-1} (a_j*a_j + 17*a_j + 58) + (4*a_n+19)
  = (196*4^n+11)/3 - 42*2^n - 2*n.
```

This value is an integer for all `n` since `4^n=1 mod 3`. The formula is mathematically derived from exact rule timings stated in the upstream source, while the local Lean proofs verify the counter transition identities and the existence/number of accelerated transitions. **The raw timing annotations themselves have not been independently formalized as counted Lean machine-step theorems**, so this is recorded as a source-dependent derivation plus reproducible computational checks. Raw simulation (starting with full synthetic tapes) agreed for every `n` from 0 through 8 inclusive, including at `n=8`: `H_2(8)=3558`, 4,270,921 defined raw transitions, and 1,790 ones at the undefined rule. The machine still has no known blank-tape halting decision.
