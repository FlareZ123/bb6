# Agent 50: P1 critical indices n ≡ 10 (mod 16)

**Status:** intermediate all-time reachability exclusion for a published BB(6) counter map, novel within the shared repository. The exact six-state Busy Beaver value remains unknown. A local Lean 4.36.0-rc2 verification now compiles every necessary Agent 1 invariant proof in full, recreated verbatim from the repository definitions and relevant theorem bodies, and checks the final target theorem with standard axioms only. A separate compilation with the unmodified GitHub files themselves is still desirable for independent integration validation.

Machine: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`; initial accelerated hub `(2,1)`.

## Main result

`BB6.Agent50P1.blank_no_residual_critical_10_mod16` proves the odd-sector feeder is unreachable. The stronger `BB6.Agent50P1.blank_no_critical_10_mod16` proves the full halting-critical hub is unreachable from actual entry `(2,1)`:

```lean
∀ k : Nat,
  ¬BB6.Agent1.Reach 2 (14*2^(16*k+10)-2*(16*k+10)-10)
```

`P1Gate.lean` includes an independent within-Agent1 reachability proof `critical_target_implies_three` for every large `d%4=2`. This closes the full critical-target exclusion in the same `Reach` relation, without requiring Agent 19's different reachability predicate. The Agent 19 raw-machine equivalence remains the known semantic bridge to the original Turing machine. This excludes the entire `n≡10 (mod 16)` class of critical indices and leaves `n≡2,6,14 (mod 16)` open.

## Complete proof architecture

Let `n=16k+10` and `s=7*2^(16k+7) - 2k - 3`, hence `s` is odd, `s≥3`, and `H(n)-6=16s+12`. Here `H(n)=14*2^n-2n-10`.

For each positive-output P1 recursive G return to `(16s+12,3)`, `P1Triple.lean` formally exhausts all possible G inputs `(k,v)`:

```text
(4s+2,8s+9), (6s+4,4s+3), (7s+5,2s).
```

A general `positive_G_feeder` lemma maps every reachable G return to its earlier even-left hub `(2k-4,v+4)`, using the already established odd-parent theorem. No candidate has G input v=1 (the exceptional c=3 branch), as each inverse theorem excludes it.

First input forces reachable `(8s,8s+13)`. Its complete G inverses:

```text
(2s-1,12s+13), (5s+2,6s+5), ((13s+7)/2,3s+1).
```

The first two force even-left hubs `(4s-6,12s+17)` and `(10s,6s+9)`, forbidden by the global reachable modular invariant (first counter 2 mod 4 and greater than 2). The last forces `(13s+3,3s+5)`, so Agent 1's even-positive classification would require `13s+15=14*2^j`.

Second input forces reachable `(12s+4,4s+7)`. Its complete G inverses are `(3s,10s+9)` and `((11s+5)/2,5s+3)`. The first is ruled out by the same mod-4 invariant, the second by an exact even-positive classification requiring `11s+13=14*2^j`.

Third input forces reachable `(14s+6,2s+4)`. The power-form classification would require `14s+18=14*2^j`, arithmetically impossible modulo 14.

Finally `P1ResidualArithmetic.lean` proves for all k both `11s+13` and `13s+15` lie strictly between consecutive powers `14*2^(16k+9)` and `14*2^(16k+10)`, so neither can equal `14*2^j`.

No search horizon, finite bound, probabilistic assumption, or `native_decide` is used by this symbolic exclusion.

## Files and reproducibility

- `P1Triple.lean`: all three exact finite G-inverse enumerations, imports the existing `GInverse.lean` and its all-input completeness theorem.
- `P1ResidualArithmetic.lean`: the parameter identity, congruences and power-sandwich theorem.
- `P1ResidualReach.lean`: proves exact G transcription inversion and the unreachable `c=3` feeders, importing `ResetGate.lean`, `P1Triple.lean`, `P1ResidualArithmetic.lean`.
- `P1Gate.lean`: proves the critical-target-to-feeder reduction and the universal unreachability of the full halting-critical hub for every `n=16k+10`.

The Lean 4.36.0-rc2 verification first compiled a signature-matching minimal import mock and then **replaced all mock axioms** with the complete original Agent 1 theorem bodies for `even_left_power_shape`, `reachable_even_mod4`, `odd_parent_general`, `T_to_two_positive`, `T_to_odd_zero`, together with the exact recursive G/T and Reach constructors, in local `PosEvenForm.lean` and `ResetGate.lean`. These were all locally compiled and audited. The resulting `P1Gate.lean` axiom output is exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. The local copies omit unrelated theorems from Agent 1's actual source, so run a final unmodified repository compile as independent reproduction; expected import order: `GParity`, `GInverse`, `PosEvenForm`, `ResetGate`, then Agent50's `P1Triple`, `P1ResidualArithmetic`, `P1ResidualReach`, `P1Gate` with all relevant directories in `LEAN_PATH`.

Known strong upstream machine bridge: `im-results/agent19-p1-source-bridge/P1HaltingBridge.lean` and [manual CI run 41388451571](https://github.com/FlareZ123/bb6/actions/runs/41388451571).

**Next decisive target:** independent full-source CI integration with unmodified Agent 1 modules, reusing Agent 19's already certified raw-machine bridge, and then attack the remaining `n≡2,6,14 (mod 16)` families. Beware earlier independent exclusion of the odd and multiple-of-four critical-index families.
