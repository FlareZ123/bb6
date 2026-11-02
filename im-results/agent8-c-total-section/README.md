# Machine C: a source-certified executable total two-counter return system

Agent 8, 2026-11-02. **Intermediate structural result, not a six-state halting decision or a determination of BB(6).**

Target machine `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` under the exact published accelerator `BB6CLine.nextC`, with blank-entry counter state `(5,0,1)`. It reaches `(5,1,0)` in precisely one successful accelerator call.

## Exact computation on two counters

`CSectionComputable.lean` defines total, directly executable `fastNext : Nat × Nat → Option (Nat × Nat)` and `fastTime : Nat × Nat → Nat` with **no noncomputable definitions or unbounded searches in either function**.

For any input `(a,k)` representing the three-counter section state `(a,k,0)`, the algorithm:

1. Takes one original Machine C accelerator step.
2. Inspects the resulting state for a halt or a return to `c=0`.
3. Otherwise scans successive actual accelerator states until the first halt or `c=0` return, using at most `4*k+4` further calls. It returns `none` exactly for a stop, or `some (a',k')` for a return.

The scanner internally records elapsed time, and `fastTime` exposes that value including the first call. The proven inequalities, **for every natural `a,k`**, are

```
1 ≤ fastTime(a,k) ≤ 4*k+5.
run originalNextC (fastTime(a,k)) (some (a,k,0))
    = (fastNext(a,k)).map (fun (a',k') => (a',k',0)).
```

The `scan0_complete` theorem proves that the fuel-exhaustion case is impossible, using the independently proved `BB6.CPhaseRank.c0_excursion_bound` theorem. `GenericScan.lean` proves the bounded scanner correct for arbitrary partial dynamical systems, including exact elapsed time and exhaustion completeness.

Concrete executable examples (checked with the same source definitions, and reproducible via Lean `#eval`):

| Section input | `fastNext` | `fastTime` |
|---|---|---|
| `(5,1)` | `some (3,4)` | 3 |
| `(3,4)` | `some (4,7)` | 7 |
| `(4,7)` | `some (20,4)` | 17 |

## Full machine-level blank-entry equivalence

The exact source Lean theorem is

```lean
BB6.Agent8ComputableC.blank_halts_iff_computable_two_counter :
  BB6.CReachBridge.RunHalts ↔
    ∃ m, BB6.Agent8Section.run BB6.Agent8ComputableC.fastNext
      m (some (5,1)) = none
```

So eventual stopping of the three-counter blank-entry accelerator is **equivalent in both directions** to eventual stopping of the explicit two-counter map from `(5,1)`. Intermediate theorem `fastNext_exact` directly witnesses a positive number of actual original accelerator steps per abstract edge. No optimistic assumption about which section was visited first is needed: the scanner selects the first encountered one.

`GenericSection.lean` proves a reusable strong-induction theorem: any deterministic section map satisfying a positive finite-step embedding law has exactly the same eventual stopping status as its underlying partial dynamics. The theorem is independent of Machine C and source-checks with only `[propext, Quot.sound]`.

An earlier `CSectionTotal.lean` gave a logically equivalent **noncomputable** two-counter map by choosing a bounded return witness; `CSectionComputable.lean` provides the preferable fully executable replacement.

## Exact Lean source and verification

- `GenericSection.lean`: generic halting equivalence for exact positive-step section maps.
- `CSectionTotal.lean`: original-source bridge, bounded section witness, exact initial-state reduction.
- `GenericScan.lean`: executable finite scanner, soundness and completeness.
- `CSectionComputable.lean`: total `fastNext` and `fastTime`, certified bounds, exact blank-entry halting equivalence.
- Source dependencies unchanged: `im-results/agent11-c-line/CLine.lean`, `im-results/agent21-c-source-bridge/CReachBridge.lean`, `im-results/agent21-c-source-bridge/CPhaseRank.lean`.
- Successful source-level [manual GitHub Actions run 41421882614](https://github.com/FlareZ123/bb6/actions/runs/41421882614), pinned Lean **4.36.0-rc2**, tested all seven modules. Final audit `blank_halts_iff_computable_two_counter`: **`[propext, Classical.choice, Quot.sound]`** and no `sorryAx`. Choice is present in *the proof* through the inherited existence theorem; the reduction functions themselves contain no classical choice.
- Manual-only workflow `.github/workflows/agent8-c-total-section.yml`. The prior noncomputable-map audit independently passed [run 41421389132](https://github.com/FlareZ123/bb6/actions/runs/41421389132).

This reduction is suitable for developing two-counter invariants, analytical return maps, quotient abstractions, and faster first-return jump formulas. It **does not by itself prove termination or nontermination**, rule out any additional blank-tape halting gateways, or improve the known numerical BB(6) lower/upper bounds. The original Cryptids raw-machine-to-counter refinement is supplied separately by Agent 21's existing source-verified bridge.
