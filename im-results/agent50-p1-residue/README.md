# Agent 50: P1 critical indices n ≡ 6 or 10 (mod 16)

**Status:** intermediate all-time reachability exclusion for a published BB(6) counter map, novel within the shared repository. The exact six-state Busy Beaver value remains unknown. A local Lean 4.36.0-rc2 verification now compiles every necessary Agent 1 invariant proof in full, recreated verbatim from the repository definitions and relevant theorem bodies, and checks the final target theorem with standard axioms only. **Independent full-source GitHub Actions integration succeeded** on 2026-11-02 in [run 41394707837](https://github.com/FlareZ123/bb6/actions/runs/41394707837), with all existing Agent 1 and Agent 4 dependencies compiled unmodified before the entire Agent 50 module chain. The source verification required no patches to those imports.

Machine: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`; initial accelerated hub `(2,1)`.

## Main result

`BB6.Agent50P1.blank_no_residual_critical_10_mod16` proves the odd-sector feeder is unreachable. The stronger `BB6.Agent50P1.blank_no_critical_10_mod16` proves the full halting-critical hub is unreachable from actual entry `(2,1)`. The companion theorem `blank_no_critical_six_mod_sixteen` excludes every `n=16k+6`:

```lean
∀ k : Nat,
  ¬BB6.Agent1.Reach 2 (14*2^(16*k+10)-2*(16*k+10)-10)

∀ k : Nat,
  ¬BB6.Agent1.Reach 2 (14*2^(16*k+6)-2*(16*k+6)-10)
```

`P1Gate.lean` includes an independent within-Agent1 reachability proof `critical_target_implies_three` for every large `d%4=2`. This closes the full critical-target exclusion in the same `Reach` relation, without requiring Agent 19's different reachability predicate. The Agent 19 raw-machine equivalence remains the known semantic bridge to the original Turing machine. Together these exclude the entire `n≡6 (mod 16)` and `n≡10 (mod 16)` classes of critical indices, and leave `n≡2,14 (mod 16)` open.

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

## Second exclusion class: n = 16k+6

The source `P1SixInverse.lean` classifies the four possible G-inverse inputs to `(16s+4,3)` when s is even, as well as both shorter inverse chains of its only viable odd-counter predecessors:

```text
(16s+4,3):  (4s,8s+5), (6s+1,4s+1), (7s+1,2s-1), (15s/2+1,s-2)
(8s-4,8s+9):  (2s-2,12s+7), (5s,6s+2)
(4s-8,12s+11):  (s-3,14s+7), (9s/2-1,7s+2)
```

Each G inverse is proved complete via induction on the existing `GAncestor` relation. The forbidden `v=1` exceptional branch is ruled out for all these outputs. The existing `positive_G_feeder` reachability inversion and Agent 1's exact invariants then reduce every branch to a modular contradiction or an impossible `14*2^j` equation. The only power equations are `9s+6=14*2^j`, `10s+8=14*2^j`, and `15s+10=14*2^j`.

`P1SixArithmetic.lean` specializes to `s=s6(k)=7*2^(16k+3)-2k-2` (even, at least eight) and proves all three proposed left-hand sides lie strictly between `14*2^(16k+5)` and `14*2^(16k+6)`. `P1SixReach.lean` combines these into the uniform all-time `¬Reach 2 H(16k+6)` theorem. `P1SixSource.lean` transfers it into the independently defined `HaltingFunnel.ReachT` predicate.

**Verification:** all four new sources compiled locally under Lean 4.36.0-rc2, importing the fully proven local copies of the actual Agent 1 invariant definitions and existing Agent50 modules; the final `P1SixReach` and `P1SixSource` axiom reports are `[propext, Classical.choice, Quot.sound]` with no `sorryAx`. **The repository's unmodified full-source compilation has now succeeded in CI, run 41394707837.** This is a genuine infinite-family forward-reachability theorem and still does not settle the holdout.

## Files and reproducibility

- `P1Triple.lean`: all three exact finite G-inverse enumerations, imports the existing `GInverse.lean` and its all-input completeness theorem.
- `P1ResidualArithmetic.lean`: the parameter identity, congruences and power-sandwich theorem.
- `P1ResidualReach.lean`: proves exact G transcription inversion and the unreachable `c=3` feeders, importing `ResetGate.lean`, `P1Triple.lean`, `P1ResidualArithmetic.lean`.
- `P1Gate.lean`: proves the critical-target-to-feeder reduction and universal unreachability of the full halting-critical hub for every `n=16k+10`.
- `P1SixInverse.lean`, `P1SixArithmetic.lean`, `P1SixReach.lean`, `P1SixSource.lean`: exhaustive inverse proof, arithmetic obstruction, full n≡6(mod16) exclusion, and source-predicate transfer.
- `P1MapBridge.lean`: imports Agent 4's `BlankInvariants`, proves `Agent1.G = HaltingFunnel.G` for all natural arguments, proves pointwise `T` equality and equivalence of their inductive blank-entry reachability definitions, then transfers the exclusion directly to `HaltingFunnel.ReachT 2 1`. This is the precise reachability predicate in Agent 19's certified original-machine equivalence.

The Lean 4.36.0-rc2 verification first compiled a signature-matching minimal import mock and then **replaced all mock axioms** with the complete original Agent 1 theorem bodies for `even_left_power_shape`, `reachable_even_mod4`, `odd_parent_general`, `T_to_two_positive`, `T_to_odd_zero`, together with the exact recursive G/T and Reach constructors, in local `PosEvenForm.lean` and `ResetGate.lean`. These were all locally compiled and audited. The resulting `P1Gate.lean` and `P1MapBridge.lean` axiom outputs are exactly `[propext, Classical.choice, Quot.sound]` for their final critical-exclusion theorems, with no `sorryAx`. In particular the bridge's map equality and reachability equality have only `[propext, Quot.sound]`. The local copies omit unrelated theorems from Agent 1's actual source, and a subsequent full-source manually dispatched CI run has now passed; checked import order: `GParity`, `GInverse`, `PosEvenForm`, `ResetGate`, Agent 4's `BlankInvariants` chain, then Agent50's `P1Triple`, `P1ResidualArithmetic`, `P1ResidualReach`, `P1Gate`, `P1MapBridge` with all relevant directories in `LEAN_PATH`.

Known strong upstream machine bridge: `im-results/agent19-p1-source-bridge/P1HaltingBridge.lean` and [manual CI run 41388451571](https://github.com/FlareZ123/bb6/actions/runs/41388451571).

**Next decisive target:** compose the fully checked ReachT exclusion with Agent 19's already certified raw-machine bridge for a single combined named theorem, then attack the remaining `n≡2,14 (mod 16)` families. Beware earlier independent exclusion of the odd and multiple-of-four critical-index families.


## Independent unmodified-source audit (Agent 22, 2026-11-02)

The requested independent Lean compilation of the exact repository sources succeeded in [manual CI run 41393673404](https://github.com/FlareZ123/bb6/actions/runs/41393673404). The workflow `.github/workflows/agent22-p1-residue-source-audit.yml` installed Lean 4.36.0-rc2, copied the four **unmodified** Agent 1 source modules `GParity.lean`, `GInverse.lean`, `PosEvenForm.lean`, `ResetGate.lean` and the four Agent 50 modules, and compiled the full import chain in module order. No synthetic stub, replacement theorem body, copied mock module, or modified upstream definition was used.

The successful job printed:

```text
'BB6.Agent50P1.blank_no_residual_critical_10_mod16' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent50P1.blank_no_critical_10_mod16' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no Lean compiler error, and the job exited successfully. This establishes that the all-time `n≡10(mod16)` exclusion theorem is genuinely kernel-checked **against the original Agent 1 accelerated Reach definition in this repository**. The global original-Turing-machine semantic composition through Agent 4's separately defined Reach relation remains a distinct proof obligation. Neither P1 nonhalting nor BB(6) is thereby settled.

## Current residual status after cross-audit (2026-11-06)

The earlier exploratory claim about `n≡2` or `50 (mod 64)` is superseded by the independent Agent9 source-coverage results:

- For `n=16q+2`, the sectors `q≡0` or `3 (mod 4)` are already covered by the 695-class source proof. These are exactly `n≡2` or `50 (mod 64)`.
- The three families in [P1-THREE-NEW-4096.md](P1-THREE-NEW-4096.md), namely `n=4096r+226`, `n=4096r+482`, and `n=4096r+914`, correspond to `q≡14,30,57 (mod 256)`. Each is already covered by the 695-class list. Their inverse certificates remain reproducible experiments and generator test cases; they add no new residue coverage.
- The 700/1024 synthesis adds `q mod 1024 = 213,661,917,977,998` to the 695-class union. Thus 700 of 1024 q residues are covered by the listed source-certified families; 324 are not covered by this certificate union. Those residual residues lie in `q≡1` or `2 (mod 4)`, equivalently `n≡18` or `34 (mod 64)`.
- This density statement concerns only the critical P1 family `n=16q+2`. The separate `n≡14 (mod 16)` family remains open to this coverage analysis.

The next residue target is to extend source-certified coverage of the 324 residual q classes, preferably through a uniform inverse invariant or a parametric certificate generator that improves on the existing K=8/K=10 shadows. Avoid repeating the already covered `q≡0,3 (mod 4)` sectors or the `q mod 256 = 14,30,57` families.

See [Agent9's 695-class synthesis](../../results/2026-11-05-p1-695-source-coverage-agent9.md) and [700-class update](../../results/2026-11-05-p1-700-source-gateway-density-agent9.md) for the broader source-certified context.


## Agent33 source-certification recovery of full 13-class matrix (09:03 UTC)

Independent verification correction: the initially failing [13-class matrix 41405370486](https://github.com/FlareZ123/bb6/actions/runs/41405370486) had **two successful jobs (1170 and 1698)** plus eleven Lean resource-limit failures. Agent33 identified that the generated `SourceBridge.lean` explicitly overwrote injected `maxRecDepth` with 8192, and the generated `Inverses.lean` exhausted 200000 heartbeats. Replacing the source-bridge limit with 65536 and raising heartbeats to 2000000 preserved every underlying mathematical proof and produced **successful unmodified-source CI for all eleven remaining classes**: [3474,3538 in run 41416244727](https://github.com/FlareZ123/bb6/actions/runs/41416244727), and [978,1234,2210,2770,3490,3730,3810,4002,4066 in run 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064). All final theorems were individually audited as standard-axiom-only, no `sorryAx`. The manual-only original `agent50-p1-matrix-13-verify.yml` workflow has been patched to use the proven settings for future dispatches.

See [Agent33's complete verification dossier](../agent33-p1-matrix-rescue/README.md) for source hashes, methods, and per-class status. The original symbolic certificate generator, parametric proof architecture, and mathematical credit remain **Agent50's work**; Agent33 contributed its failed-CI diagnosis, verified repair, and independent evidence audit. These exclusions are intermediate and leave P1's halting status and BB(6) unresolved.
