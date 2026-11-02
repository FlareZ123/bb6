# Agent 1: authentic reset ancestry and sparse even-counter reachability in P1

**Status (2026-11-02): all theorem files compiled by the original-source manual Lean CI; an intermediate global reachability result, not a P1 or BB(6) decision.** The six-state machine is `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, and the exact published accelerated map is `BB6.Agent1.T` with blank-entry state `(2,1)`. The source-to-original-TM equivalence is a separate previously certified dependency documented in `im-results/agent19-p1-source-bridge/`.

## Main complete all-time theorems

The file `EvenSeed.lean` proves `even_hub_reset_seed` for every `Reach b d` with even `b` and positive even `d`:

```
∃ j s : Nat,
  Reach 2 s ∧ b + 12 = 14 * 2^j ∧ s + 2*j + 2 = b + d.
```

The reset state `(2,s)` is **actually reachable from blank**. The proof traces the positive-even sector backwards through the exact two-transition macro `(x,y) -> (2x+12,y-x-10)`. This refines Agent 1's previously proved `even_left_power_shape` by preserving the *actual reset origin* and an exact conservation equation. It is not a claim that every synthetic tuple satisfying the equation is reachable.

`EvenMiss.lean` proves `reachable_even_two_odd_exponent`: if a reachable state has even first counter `b` and right counter exactly `2`, then some **odd** natural `j` satisfies `b+12=14*2^j`. The even-index contradiction uses the existing authentic `reset_four_power` theorem and the strict gap between adjacent `14*2^k` powers. It also excludes exceptional `Reach 2 2` by exhausting both predecessor cases.

`ResetOdd.lean` proves `reset_divfour_requires_even_two` and `reset_divfour_odd_exponent`. For every actually reachable reset `Reach 2 s` with `s>=12` and `s%4=0`, some **odd** natural `t` satisfies `s+8=14*2^t`. The c=1 predecessor branch is impossible by the existing reachable even-left mod-four invariant; the remaining c=2 branch reduces to the odd-exponent theorem.

`EvenLow.lean`, `EvenFull.lean`, and `EvenSparse.lean` combine these facts into a **global sparse classification**. The principal `even_hub_sparse_counter_classification` theorem states that every reachable even-left, positive-even-right hub has an exponent `j` with `b+12=14*2^j`, and whenever `j>=2` and `d%4=(2*j+2)%4`, there is an **odd** `t>=j` satisfying

```
d + 14*2^j = 14*2^t + 2*j + 6.
```

This is a quantified all-time necessary condition with no finite trajectory bound. Hence at fixed `j`, right counters in that residue class are restricted to a sparse exponential ladder. Two source-checked consequences:

* **Even `j>=2`:** no such reachable right counter below `14*2^j+2*j+6` (an exponential-sized forbidden wedge).
* **Odd `j>=3`:** below `42*2^j+2*j+6`, the **only** possible right counter in that residue is `d=2*j+6` (a necessary exception, *not* a construction or proof of reachability).

The earlier `even_hub_low_residue` gives a parity restriction in the linear band `d<2j+6` without distinguishing even and odd `j`; the stronger arithmetic theorem subsumes much of that case.

## Verification

All six new source modules `EvenSeed, EvenMiss, EvenLow, ResetOdd, EvenFull, EvenSparse` import **unmodified** original repository `PosEvenForm` and `ResetGate` definitions. The repository's manual-only workflow `.github/workflows/agent1-reset-lean.yml` compiled the complete import chain under Lean **4.36.0-rc2** and printed axiom audits for every theorem. The successful [GitHub Actions run 41441234692](https://github.com/FlareZ123/bb6/actions/runs/41441234692) at source commit `fdb26579e139cad0dab6c43128f9abdcdb1a36ef` verifies all named theorems with exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, custom axiom, mocked predecessor, `native_decide`, or unsafe computation is present in the repository sources. Earlier [run 41440848185](https://github.com/FlareZ123/bb6/actions/runs/41440848185) independently checked through `EvenFull`.

A local development copy temporarily replaced four predecessor lemmas with signatures matching proven `ResetGate` lemmas while writing proofs. **This local stub was never committed.** The successful CI run recompiles the full original `ResetGate.lean` before every new theorem and is the authoritative check.

## Relationship to the unsolved halting question

Agent 19 previously proved the original raw machine halts iff the genuine blank-entry P1 map reaches a sparse critical reset `(2,H(n))` with `H(n)=14*2^n-2n-10`. Existing source-certified exclusions leave the infinite candidate index sectors `n≡2,14 (mod 16)` (and already-excluded small cases). These new results constrain **positive-even-right hubs and reset origins**, which can be terminal leaves of a backward inverse cone. They do **not** give a complete invariant for positive-odd-right hubs, where genuine unbounded-depth synthetic inverse chains exist in *both* remaining critical index sectors (Agents 27 and 45). No blank-reachability or nonhalting result for those sectors follows from this work.

Potential follow-up: integrate the sparse right-counter ladder as an additional exact all-time rejection criterion into Agent 47's finite-G-inverse proof generator or Agent 4/45's affine P1 cone certificates; evaluate whether any stubborn even-right power-shaped branch is pruned. Develop an odd-right reachability grammar controlling the upper-chain roots; this is the genuine closure bottleneck. Novelty relative to external literature has not been established. These findings properly remain in `im-results/`, and no BB(6) bound change is claimed.
