# D3 blank root: source-certified 1711-return I5 checkpoint

**Status:** intermediate original-source Lean certificate. This is a finite blank-root lower bound for the literal rooted D3 machine, not an eventual halting/nonhalting decision and not a BB(6) champion or upper bound.

## Result

Let

```
T = 15 + DRegular.accumulated 1711 DRegular.seed5.
```

The literal D3 rooted machine

```
1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---
```

has no undefined transition at any exact time `n ≤ T`. The source-authenticated bound is proved in `I5Root1711.lean` by composing:

1. the D3-to-D0-B exact halting-time conjugacy and D3's 15-step blank-to-I5 prefix from Agent 3;
2. Agent 19's exact first-halting-time bridge from the raw D3 root to the original `CryptidBoundary` unary source `sourceUnary 5`;
3. Agent 35's 1711-step arithmetic seed5 endpoint and the original-source `DRegularSource.first1711_source`;
4. Agent 2's already accepted `BB6.ERemaining.source_contract` (original-source CI 41712102615), instantiated here rather than reproved;
5. the fact that source state 6 is absorbing, while the 1711-return endpoint is live state F and its next transition is also live.

Lean also proves `10^1458 ≤ T < 10^1459`, so the certified horizon has exactly 1,459 decimal digits. The theorem `parsed_D3_no_halt_10pow1458` is the readable numerical corollary.

## Evidence boundary

The proof does not infer a blank-root trajectory from the arithmetic model alone. The exact root-time bridge is the Agent 19 theorem `parsed_D3_exact_source_time`, and the original-source transport is instantiated with `BB6.ERemaining.source_contract`. The final theorems print their transitive axiom dependencies; the manual workflow rejects `sorryAx`.

The result concerns D3 only. It does not settle the other three rooted D-family machines, prove D3 eventually halts, or prove D3 never halts. It is stored in `im-results/`, not `results/`, because it is a finite root-specific prefix rather than a complete BB(6) classification.

## Reproduction

Run the manual workflow `.github/workflows/agent35-d3-i5-root-prefix.yml`. It reconstructs the exact DRegular and ERemaining archives, compiles the original Cryptid boundary and padding modules, compiles the Agent 3/19 raw-root and source bridges, then checks this module under Lean 4.36.0-rc2.


## CI result

**Passed:** [GitHub Actions run 45381457744](https://github.com/FlareZ123/bb6/actions/runs/45381457744), Lean 4.36.0-rc2. The workflow compiles the original source dependency chain, prints the theorem axiom reports, and fails if `sorryAx` occurs. It passed with no `sorryAx`.

The exact no-halt theorem is now source-kernel verified for the literal parsed D3 blank-root machine. The numerical corollary covers all exact times through (10^{1458}); the stronger symbolic horizon is (T=15+\operatorname{accumulated}(1711,\mathrm{seed5})), with (10^{1458}\le T<10^{1459}).
