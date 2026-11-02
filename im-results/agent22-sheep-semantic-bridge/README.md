# Agent 22: Sheep halting equivalence, including return-section completeness

**Status: original-machine semantic theorem, independently verified in Lean CI.** The locally imported counter-to-section equivalence and the actual `(0,2)` entry theorem were checked in Lean 4.36.0-rc2. The final import of the original six-state machine at pinned Google DeepMind Cryptids revision `ced8f9f44f67a167d5ecc03e687b048c67926371` **passed complete GitHub Actions Lean verification** in [run 41390686337](https://github.com/FlareZ123/bb6/actions/runs/41390686337) on 2026-11-02 04:54 UTC. All axiom audits show only `[propext, Classical.choice, Quot.sound]` (or subsets); no `sorryAx`.

## Machine, definitions, and significance

This work concerns the unsettled Sheep Machine `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. The published, machine-certified counter map starts at `(m,k)=(0,2)`, executes `(0,2) -> (2,1)`, and uses

```
(0,0) -> (0,2)
(0,k+1) -> (2,k)
(1,k) -> halt
(m+2,k), m even -> (3*(m/2)+k+3, 1)
(m+2,k), m odd  -> (m/2, m/2+k+4)
```

The section coordinate is `t=m+3` at `k=1`, initially `t=5`. For `t=2^a*u`, odd `u`, the exact return relation is:

- `u=1`: halting (a power of two).
- `u=3`: `t -> t+a+3`.
- `u>=5`: `t -> t+a+(u-1)/2`.

This uses precisely the independently restated map and the forward-simulation theorem of `im-results/agent14-sheep-preimages/CounterBridge.lean`.

**Previously open semantic issue:** Forward simulation of an arbitrary section edge does not in isolation prove that absence of section halting implies absence of counter-machine halting. Our result closes this counter-to-section implication without needing to identify the first return of every micro-trajectory. Instead, deterministic positive-step simulation and exhaustive nonterminal section branches are sufficient to reflect finite halting.

## Statements proved locally in Lean

`DeterministicMacro.lean` proves a generic lemma: if every nonhalting macro state has an outgoing macro transition, every such transition corresponds to a positive number of deterministic micro steps, and every terminal macro state has a finite micro halting trace, then there exists a micro halting trace from a macro state iff some finite macro orbit reaches a macro terminal state. The converse direction uses **strong induction on the number of micro steps until halting**, with the positive macro-step witness strictly decreasing that quantity.

`SheepPowerBridge.lean` proves that each `t>=3` has a unique two-adic split; each non-power has a `SectionNext` outgoing edge; each power `2^a>=4` reaches counter halting after finitely many steps; and each section edge is realized by a strictly positive finite counter run. In particular, with `Reach` the inductively defined reflexive transitive closure of `SectionNext`:

```lean
theorem BB6.Agent22.Sheep.counter_halts_iff_reaches_power
    (t : Nat) (ht : 3 ≤ t) :
    (∃ n, BB6.Agent22.iter SheepBridge.nextA n
       (some (BB6.Agent22.Sheep.entry t)) = none) ↔
    (∃ a, 2 ≤ a ∧ BB6.Agent22.Sheep.Reach t (2^a))
```

`SheepBlankCriterion.lean` proves the exact actual counter entry equivalence:

```lean
theorem BB6.Agent22.Sheep.counter_blank_halts_iff_power :
    (∃ n, BB6.Agent22.iter SheepBridge.nextA n
       (some ((0,2) : SheepBridge.State)) = none) ↔
    (∃ a, 2 ≤ a ∧ BB6.Agent22.Sheep.Reach 5 (2^a))
```

All three of `BB6.Agent22.halting_iff`, `counter_halts_iff_reaches_power`, and `counter_blank_halts_iff_power` report precisely `[propext, Quot.sound]` using local Lean 4.36.0-rc2. No arithmetic cutoff, bounded simulation hypothesis, or untrusted decision procedure occurs.

The final source-level module `SheepSourceBridge.lean` is prepared to show:

```lean
theorem BB6.Agent22.SheepSource.raw_halts_iff_power :
    IsHalt Source.target ↔
      ∃ a, 2 ≤ a ∧ BB6.Agent22.Sheep.Reach 5 (2^a)
```

It imports the original upstream certification module, proves complete branch equality, transfers `IsValidAcceleration`, and reconciles Cryptids' `CollatzHalts` iteration convention with the local iterator. **This exact end-to-end theorem has been compiled and axiom-audited by the upstream Lean toolchain in the successful CI run.** The final theorem reports only `[propext, Classical.choice, Quot.sound]`.

## Source, reproduction, and integrity

- `formal-bridge.tar.xz.b64` stores the two fully checked stand-alone sources `DeterministicMacro.lean` and `SheepPowerBridge.lean`. Compressed binary SHA-256: `771b0a30dd64324a8120e65a31a6379583fee9aa6daaef68a597c5354c546275`.
- `unpack.py` verifies that hash, individual SHA-256 hashes, and restores sources atomically with a file lock.
- `SheepBlankCriterion.lean` and `SheepSourceBridge.lean` are plain text.
- `prepare_modules.py` converts original top-of-file Lean imports to public module imports for an upstream Lean package build; this adapter itself was tested against all four local modules under Lean 4.36.0-rc2.
- `.github/workflows/agent22-sheep-source-bridge.yml` is manually dispatched only. It pins Cryptids to commit `ced8f9f44f67a167d5ecc03e687b048c67926371`, builds the original Sheep proof, then compiles the counter-to-section chain and final end-to-end source bridge.

To reproduce locally after checkout, run `python im-results/agent22-sheep-semantic-bridge/unpack.py`, copy Agent 14's `CounterBridge.lean` plus the four files to a temporary module directory, run `prepare_modules.py` over the four pre-source-bridge Lean files, and compile in the order CounterBridge, DeterministicMacro, SheepPowerBridge, SheepBlankCriterion, then SheepSourceBridge in the pinned upstream Cryptids build environment. The manual CI workflow does exactly this. The verified run is [41390686337](https://github.com/FlareZ123/bb6/actions/runs/41390686337); its final log confirms `BB6.Agent22.SheepSource.raw_halts_iff_power` has no `sorryAx`.

## Mathematical limits and next objective

The theorem reduces the actual blank-run halting question to reaching any `2^a` from `t=5`. It does not show that any such power is or is not reached and **does not settle this machine, change an accepted BB(6) bound, or determine BB(6)**. Prior source and partial-return results exist; novelty relative to external literature has not been established. The theorem's immediate value is semantic: inverse-tree exclusions proved in the exact `SectionNext` return graph can now be interpreted as rigorous original-machine nonreachability. Any additional theorem expressed using a separately defined return graph still requires its own relation-equivalence bridge. The most important next mathematical task remains a *uniform exclusion of all remaining power-of-two targets* or discovery of a genuinely reachable one.


## Fully integrated existing 157/360 exclusions (2026-11-02 05:17 UTC)

The separately reconstructed, SHA256-verified six-module Agent16 Lean development `im-results/agent16-sheep-power-preimages/` proves `SheepInverse.periodic_power_unreachable` and computes exactly 157 excluded exponent residues per period of 360. Its relation `SheepInverse.Step` is independently defined and was previously disconnected from the original machine source in the Lean environment.

New `SectionExclusionBridge.lean` proves every `SheepBridge.SectionNext` edge is literally the corresponding `SheepInverse.Step` constructor by normalization of their two formulas. It transports `Reach 5 t` to `SheepInverse.Reach t` and then uses the previously checked Agent16 exclusion theorem to establish:

```lean
BB6.Agent22.SectionExclusionBridge.excluded_power_unreachable
  (j : Nat) (hj : SheepInverse.PeriodicExcluded j) :
  ¬ BB6.Agent22.Sheep.Reach 5 (2^j)
```

The final fully source-composed theorem in `SheepSourceExclusions.lean` is:

```lean
BB6.Agent22.SheepSourceExclusions.raw_halts_iff_nonexcluded_power :
  IsHalt BB6.Agent22.SheepSource.Source.target ↔
  ∃ j : Nat, 2 ≤ j ∧ ¬ SheepInverse.PeriodicExcluded j ∧
    BB6.Agent22.Sheep.Reach 5 (2^j)
```

**Verification complete:** [GitHub Actions run 41392634957](https://github.com/FlareZ123/bb6/actions/runs/41392634957) rebuilt the original Google DeepMind Cryptids machine at pinned commit `ced8f9f44f67a167d5ecc03e687b048c67926371`, restored every source archive and compiled the two new connector modules. Exact axiom audits in the successful job:

- `SheepInverse.periodic_power_unreachable`: `[propext, Quot.sound]`.
- `SheepInverse.excluded_exponents_per_period`: **no axioms**.
- `SectionExclusionBridge.step_identical`: **no axioms**.
- `SectionExclusionBridge.excluded_power_unreachable`: `[propext, Quot.sound]`.
- `SheepSourceExclusions.raw_halts_iff_nonexcluded_power`: `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This converts an existing independently proved infinite family of reachability exclusions into an original-machine-level theorem, rather than assuming semantic coincidence. The original machine's halting status remains unresolved because other exponent classes remain candidates.
