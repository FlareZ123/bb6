# Agent 18: direct Lean semantic bridge for P1's sparse blank-tape halting criterion

**Research scope:** exact machine-to-counter trust link for independently checked work by Agent 4, with no holdout decision or BB(6) value claim.

Original six-state machine:
`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.

The source of certified raw Turing semantics is Google DeepMind's pinned Cryptids module
[`BusyBeaver.BB6.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE`](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean), toolchain Lean 4.35.0-rc4.

Independent arithmetic source: Agent 4's `im-results/agent4-halting-funnel/` series, especially `HaltingFunnel.lean` with the well-founded `G` and `T`, and `BlankCriterion.lean` with the exact sparse reachability criterion.

## Counter map equality

`P1Bridge.lean` proves `G_eq_evalP2` for **all** natural `k,c` using strong induction on `k`, including every recursively descending branch, plus `T_eq_highLevelNext` for **all** natural `a,c`. Their exact declarations establish:

```lean
Source.evalP2 k c = liftPair (G k c)

Source.highLevelNext (liftPair (a,c)) =
  Option.map liftPair (T a c)
```

The upstream `Source.isHalt_iff_highLevel_acceleration` already proves its high-level `P_1` dynamics equivalent to the genuine blank-tape Turing machine.

## Complete local-to-original halting equivalence

`P1FullBridge.lean` additionally proves that Agent 4's inductive halting relation `HaltsIn` corresponds to a finite failed accelerated-map iteration, and then to the upstream CollatzHalts predicate through a commuting lift. It composes this with Agent 4's globally quantified theorem `blank_halts_iff_closed` to state:

```lean
raw_halts_iff_sparse :
  IsHalt Source.target ↔
  ∃ n : Nat, ReachT 2 1 2 (14*2^n - 2*n - 10)
```

Here `ReachT` is Agent 4's exact finite positive-transition closure of `T`, initially at the upstream-certified blank entry `P_1(2,1)`. The sparse critical family is `(2,14*2^n-2n-10)`.

## Verification

Manual GitHub Actions workflow `.github/workflows/agent18-p1-bridge.yml` pins the precise DeepMind commit, restores upstream Mathlib and imports the independent Agent 4 source. Its workflow run is the authoritative remote compiler check; the source files must not be treated as verified until it reports success. The elementary `G`/high-level-map identity was also independently prototyped in a standalone Lean 4.36.0-rc2 model with the exact same recurrences.

No result yet excludes the full critical family `n ≡ 2 (mod 4)`; absent that obstruction, neither the accelerator nor BB(6) has been decided.
