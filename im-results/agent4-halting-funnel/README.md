# Agent 4: an infinite halting funnel in a formally accelerated BB(6) holdout

**Status: mathematical intermediate result concerning synthetic initial configurations.** This does not prove that the blank-tape computation halts, does not classify the holdout, and does not change the known bounds for BB(6). Keep under `im-results/` unless a decisive blank-tape link or genuinely frontier-advancing theorem is found.

## Machine and independently published reduction

Machine: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` (initial state A). The Lean-certified reduction from DeepMind:
https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean

Published configuration: `P1(a,c) = 0∞ 1^a A> 1^c 0∞`. Its accelerated map `T` and auxiliary recursion `G` are restated literally in `HaltingFunnel.lean`. The formal theorem here concerns this independently restated `T`. DeepMind separately proves equivalence of its accelerator to the Turing machine.

## Kernel-checked theorem

For each natural number `n`, set

```text
A_n = 14 * 2^n - 2*n - 11
E_0 = 2; E_(j+1) = 2*E_j + 12
C(j,0) = 4; C(j,n+1) = C(j+1,n) + E_j + 10
```

Then `A_n = C(0,n)-1`, and starting from the synthetic state `P1(A_n,0)`, the accelerated map executes exactly `2*n+2` nonhalting transitions and then halts on the following call. Equivalently, `HaltsIn (2*n+3) A_n 0`, where the last call evaluates to `none` and is included in the count.

The proof is by induction over the funnel stages. At `(E_j,C(j,n+1))`, the next two accelerated transitions are

```text
(E_j, C(j,n+1))
 -> (E_j+3, C(j,n+1)-2)
 -> (E_(j+1), C(j+1,n)).
```

The second transition is the nonrecursive `G` branch, justified for all parameters by the exact lower bound `C(j+1,n) >= 4`. At the endpoint `(E_n,4)`, the next transition reaches `(E_n+3,2)`, which is the halting gate. The induction proves every parameter value, not just a finite scan.

Files: `HaltingFunnel.lean` holds the all-natural-number theorem `halts_from_zero_exact`, the closed-form lemma `A_closed`, and the transition lemmas. It compiles using Lean **4.36.0-rc2** importing only `Std`; `#print axioms` reports `[propext, Quot.sound]` and no `sorryAx`. Run `lean im-results/agent4-halting-funnel/HaltingFunnel.lean` with that Lean version.

Examples:

| n | A_n | Raw TM transitions until halting (finite experiment) |
|---:|---:|---:|
| 0 | 3 | 36 |
| 1 | 15 | 200 |
| 2 | 41 | 924 |
| 3 | 95 | 3,944 |
| 4 | 205 | 16,260 |
| 5 | 427 | 65,984 |
| 6 | 873 | 265,788 |
| 7 | 1767 | 1,066,808 |
| 8 | 3557 | 4,274,484 |
| 9 | 7139 | 17,112,368 |
| 10 | 14305 | 68,478,252 |

The raw transition counts are observed by an independent direct 6-state tape interpreter, including the initial synthetic tape. Using the raw per-rule costs printed as comments in the DeepMind source, they fit the algebraic formula
`(196*4^n -84*2^n -12*n -4)/3`. This raw-step cost identity is **not** presently kernel-checked for all `n`; the Lean theorem rigorously proves the accelerated transition count.

## Scope and direction

The actual blank-tape orbit starts at `P1(2,1)`, not at an arbitrary `P1(A_n,0)`. Direct simulation over two million `T` transitions saw no halting gate, and a scan of all odd `a <= 5,000,000` found precisely the 19 `A_n` in that range that halt before the accelerated orbit first leaves even-`c` states. Those scans are empirical and not a completeness proof.

The interesting remaining question is whether the blank-tape orbit can enter this funnel, or any other halting basin, and whether there are meaningful invariants of the reachable `c=0` states preventing that. Avoid interpreting the synthetic family as evidence of blank-tape halting or a BB(6) bound.

**Reproducibility:** `HaltingFunnel.lean` is the fully checked symbolic proof; `verify_raw.py` separately checks the first nine cases through the raw transition table.


## Additional kernel-checked converse: exact even-sector classification

`EvenSector.lean` strengthens the earlier one-sided construction to a necessary-and-sufficient classification for **all accelerated trajectories starting at `P1(a,0)` that halt while every visited hub has even second coordinate `c`**:

```text
(there exists a finite halting T trace from (a,0), with c even at every hub)
    if and only if
(there exists n >= 0 such that a = 14*2^n - 2*n - 11).
```

The theorem is `even_trace_from_zero_iff` and holds for arbitrary natural `a`. It is fully checked in Lean 4.36.0-rc2. `#print axioms` reports `[propext, Classical.choice, Quot.sound]` with no `sorryAx`. `EvenHIn` explicitly encodes a sequence of T evaluations ending at `none` while every reached hub (including the initial and final hub) has even `c`. The full converse is important: the numerical scan of odd inputs up to 5 million is replaced by an all-natural-number theorem for precisely stated even-c traces.

Proof idea: From even `a,c` the accelerated dynamics have exactly four outcomes: at `c=4` hit the halting gate; at `c=2` return through the even-sector reset `(2,a+4)`; for even `c>=6` with `c>=a+10` make the two-call growth step `(2a+12,c-a-10)`; in the remaining cases the trajectory exits into odd `c` and therefore is excluded by the trace predicate. Formalized parity lemmas prove this is exhaustive even through the recursive `G` branch. Every potential reset from an `E_j` growth state leads to `(2,E_j+4)`; `reset_disjoint` proves `E_j+4 != C(0,m)` for all `j,m`, eliminating all reset-assisted halts. Backward induction then yields exactly the explicit `C` thresholds.

**Reproduction:** Compile `HaltingFunnel.lean` into a Lean object file under the Lean module search path; then compile `EvenSector.lean` with that object available. Both sources use only the bundled `Std`. In our local test the two-file compilation succeeded; neither file contains `sorry`.

This theorem still does **not** classify trajectories that later encounter odd `c`; those trajectories include the actual blank-tape orbit. The full BB(6) question remains open.

## Kernel-checked gateway for the actual odd-counter orbit

Two further sources added:

- `OddReturn.lean`, importing `EvenSector`, gives an exact two- or three-call return map `U` for all odd `c` and even `a`. Theorems `U_one`, `U_three`, and `U_large` prove the step-for-step relation to published `T`. The theorem `U_left_even` proves that every return lands at even `a`. The theorem `U_even_counter_iff_three` proves `(U(a,c)).2` is even **if and only if** the input odd `c` equals 3, isolating the gateway into the even-counter sector. Finally, `U_three_closed_iff` states that once the return begins at `(a,3)`, the resulting `(2,a+6)` halts while remaining in even-c hubs exactly if `a+2n+16=14*2^n` for some natural `n`. Both the return and clean-halt criteria are kernel checked, no `sorryAx`, standard axioms only.
- `GModular.lean`, importing `HaltingFunnel`, proves a residue dichotomy for all input `c≡1(mod 4)`: its output `(a',c')` has either `(a' mod8,c' mod4)=(0,1)` or `(4,3)`. This theorem is valid for every `k` and the full recursive `G`, not just finite samples.

These results are a tractable phase reduction for the real blank-start orbit, with the remaining key obligation to prove that the concrete orbit never reaches a clean-halting gateway. They **do not** prove nonhalting. Compile `OddReturn.lean` after the first two compiled Lean modules; `GModular.lean` imports the first module only.


## Kernel-checked global blank-entry criterion (strongest result as of this update)

`Reachability.lean` proves that a `T` transition starting at an odd right counter can enter an even right counter only at `c=0`. At `c=0`, the next hub always has first counter 2. 

`BlankCriterion.lean` proves the **full global biconditional** on the real blank-tape entry `P1(2,1)`:

```text
(∃ finite halting T trace from (2,1))
    ↔
(∃ n, finite T trajectory from (2,1)
          reaches (2, 14*2^n - 2*n - 10)).
```

Formal theorem `blank_halts_iff_closed`, checked with Lean 4.36.0-rc2 and standard axioms only. The proof is an all-natural strong induction on halting-trace length: the odd-c sector keeps odd c or passes through zero, zero creates a new hub with a=2, and a positive even-c excursion either halts entirely in that sector (classified by `EvenSector.lean`) or reaches an odd-c hub with a shorter halting suffix. The converse uses the previously proved halting funnel and finite reachability concatenation.

This is the formally verified version of the corresponding *informal* reduction in Agent 1's `im-results/agent1-p1-map/PHASE-CLASSIFICATION.md`. It is a genuinely blank-entry-relevant theorem, but it does not establish reachability or nonreachability of this infinite set. There is **no proof of BB(6)**.

`BlankInvariants.lean` proves a reachable-state modular invariant from the actual initial hub: when a reached hub has positive c and even a, then either `a=2` or `a≡0 (mod 4)`. Its `BlankReach` forward-closure relation is proved equivalent to `ReachT 2 1` from `BlankCriterion.lean`.

`NoFirstTarget.lean` proves **`blank_ne_first_critical : ¬ BlankReach 2 4`**, excluding the first member `(2,4)` of the critical family from the real blank orbit, for all finite times. The proof classifies all predecessors: `(2,4)` can only follow `(3,0)`, which can only follow `(1,1)` or `(0,2)`. Both are globally impossible successors under the exact `T`. This is a genuine all-time reachability exclusion, though a very small part of the infinite target set.

`Mod8Gateway.lean` proves a residue restriction on `G`: if `k` is even and `c` odd, then `G(k,c).2 = 3` implies `G(k,c).1 ≡ 4 (mod 8)`. This helps analyze the observed odd reset mod-8 pattern without claiming it globally.

To verify the whole chain, compile successive Lean object files in this order with `LEAN_PATH` pointing to their output directory: `HaltingFunnel.lean`, `EvenSector.lean`, `OddReturn.lean`, `Reachability.lean`, `BlankCriterion.lean`, `BlankInvariants.lean`, `NoFirstTarget.lean`. `GModular.lean` imports the first module and `Mod8Gateway.lean` imports `GModular`. Each final theorem's `#print axioms` shows standard Lean axioms and no `sorryAx`. Machine-to-counter semantic correctness is separately proved by the cited Google DeepMind module; this standalone proof series restates the counter map without importing DeepMind's package.
