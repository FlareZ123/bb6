# Agent 19: certified original-machine to sparse P1 halting criterion

**Status:** intermediate, fully kernel-checked connection of existing published and local results. It improves auditability and reuse, while leaving the actual halting status of this holdout unresolved. It establishes no new BB(6) bound or exact value.

Original six-state two-symbol machine:
`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.

## Final checked theorem

The original blank-tape machine halts **if and only if** the accelerated trajectory of its published `P1` section, beginning at `(2,1)`, can reach a member of the infinite sparse family:

```lean
theorem BB6.P1Bridge.raw_halts_iff_sparse_gate :
    IsHalt Source.target ↔
    ∃ n, ReachT 2 1 2 (14*2^n-2*n-10)
```

The `Source.target` definition is imported directly from the pinned original Turing-machine module, rather than a reconstructed table. `ReachT` is the finite reachability relation for the exact independent `T` accelerator in Agent 4's source.

**Independent CI check:** [GitHub Actions 41388451571](https://github.com/FlareZ123/bb6/actions/runs/41388451571), completed **successfully 2026-11-02 04:29 UTC**. The final theorem reported only the standard axioms `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, `sorryAx` or external oracle occurs in the checked theorem. Source revision `ced8f9f44f67a167d5ecc03e687b048c67926371` of [Google DeepMind Cryptids](https://github.com/google-deepmind/cryptids) and Lean `v4.35.0-rc4` were fixed in the workflow.

## Exact proof dependencies

1. `P1Bridge.lean` imports upstream `BusyBeaver.BB6.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE` and Agent 4's `HaltingFunnel`. `G_agree` proves **for every** natural `k,c`, via strong induction on `k`, that the local recursive drain `G` exactly matches upstream `evalP2` under a state lift. `T_agree` proves **for every** natural `a,c` the entire six-case local `T` matches upstream `highLevelNext`, using the `G_agree` lemma in both recursive branches.
2. `valid_local` transports the upstream theorem `is_valid_highLevel_acceleration` to the local map, thus providing a kernel-checked `IsValidAcceleration Source.target (2,1) encodeLocal nextLocal`. Its consequence `raw_halts_iff` connects raw blank-tape halting to `CollatzHalts nextLocal (2,1)`.
3. `P1HaltingBridge.lean` proves finite local `HaltsIn` traces agree **in both directions** with the library's `CollatzHalts` iteration. Induction uses the exact absorbing-None semantics of `Option.bind` and the iteration successor lemma.
4. The final theorem composes those semantics with Agent 4's independently checked `blank_halts_iff_closed` theorem (which itself imports the exact even-sector trace characterization).
5. To preserve the legacy Lean file bodies while importing them from the published `module` system, `prepare_modules.py` promotes only their initial import and adds the required public section in the **isolated CI working directory**. The checked proof body is unchanged and the shared original source files are untouched.

## Reproduction

Run the **manually dispatched** workflow `.github/workflows/agent19-p1-bridge.yml` on `main`. It installs the pinned Lean release, checks out the exact upstream source commit, restores Mathlib cache, builds upstream certified P1, copies the five Agent 4 modules `HaltingFunnel`, `EvenSector`, `OddReturn`, `Reachability`, `BlankCriterion`, then compiles both bridge files. It prints an axiom audit of the final theorem. This workflow has no automatic trigger.

The complete original-manuscript chain can also be read from:

- `im-results/agent4-halting-funnel/BlankCriterion.lean` and its dependencies;
- `im-results/agent19-p1-source-bridge/P1Bridge.lean`;
- `im-results/agent19-p1-source-bridge/P1HaltingBridge.lean`.

## Outstanding research obstruction

The result transforms the original machine's stopping question into the **exact** one-dimensional family of reachable targets. It establishes neither reachability nor exclusion of every target. Agent 12's `AllOddCritical.lean` and `AllFourCritical.lean` eliminate all odd indices above one and all nonzero indices divisible by four, respectively; small early targets also have exact exclusions. The essential unsolved infinite class remains `n≡2(mod4)`, despite some finite exclusions.

Any proposed complete P1 nonhalting proof can now prove the sparse target family unreachable and compose with this already checked raw-machine theorem. The exact BB(6) value, universal upper bound, and this machine's blank-tape decision all remain unknown.
