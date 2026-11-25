# Candidate complete exclusion of the n=10 terminal-cancellation corridors

**Status: Lean CI compiled; no `sorryAx` in the dependency chain.** Focused workflow run `45721351121` compiled the pinned source machine, `Agent49ParitySource`, `SquareGapTerminalBridge`, `Agent8RootCancellationBudgetBridge`, `RootExclusion`, and `RootMassGapAllN10`. The concrete root checkpoints use `native_decide`, so axiom reports include generated native evaluator axioms; this is not a kernel-reduction-only proof. The four ray bridge exclusions and the special even gap-two branch consumer all compile.

## Two ratio geometries from the cancellation bridge

For a predecessor state with smaller coordinate (m), the n=10 ternary band is
`19680 = 3^9-3 <= m <= 3^10-4 = 59045`.

The four terminal-window / previous-ray combinations reduce to two predecessor geometries:

- Far previous ray: `|L-13m| <= E`.
- Near previous ray: `|4L-7m| <= E`.

The current bridge uses `E <= 35*n+120 = 470` at n=10. Here (L) is the larger coordinate.

## Near 7:4 corridor

From `|4L-7m|<=470`,
`11m-470 <= 4(L+m) <= 11m+470`.
For `19680 <= m <= 59045`, integer total mass therefore satisfies
`54003 <= L+m <= 162491`.

The source-transcribed root masses at steps 33 and 38 are:
- step 33: D(19954,27733), mass 47687;
- step 38: D(44634,124427), mass 169061.

Thus a root state in the near corridor must be one of steps 34–37. The source-transcribed intermediate states and exact 7:4 residuals are:

| step | state | `|4L-7m|` |
|---:|---|---:|
| 34 | D(7784,59872) | 185000 |
| 35 | D(52084,23375) | 44711 |
| 36 | D(28698,70161) | 79758 |
| 37 | D(41468,86104) | 54140 |

Every residual exceeds 470.

## Far 13:1 corridor

From `|L-13m|<=470`,
`14m-470 <= L+m <= 14m+470`.
For `19680 <= m <= 59045`, total mass lies in
`275050 <= L+m <= 827100`.

The source-transcribed root masses at steps 39 and 46 are:
- step 39: D(79788,133932), mass 213720;
- step 46: D(426044,571540), mass 997584.

Thus a root state in the far corridor must be one of steps 40–45. The source-transcribed intermediate states and exact 13:1 residuals are:

| step | state | `|L-13m|` |
|---:|---|---:|
| 40 | D(54138,239399) | 464395 |
| 41 | D(185262,162438) | 1926432 |
| 42 | D(22822,487342) | 190656 |
| 43 | D(464518,68489) | 425839 |
| 44 | D(396018,205505) | 2275547 |
| 45 | D(190506,616551) | 1860027 |

Every residual exceeds 470.

## Formal proof structure

The draft `RootMassGapAllN10.lean` now contains the exact-checkpoint declarations and the two root ratio-strip consumers, plus four bridge-level wrappers matching the current `RootCancellationBudgetBridge.lean` hypotheses:
- `n10_far_far_bridge_excluded`;
- `n10_far_near_bridge_excluded`;
- `n10_near_far_bridge_excluded`;
- `n10_near_near_bridge_excluded`.

Each wrapper derives the relevant ratio strip from the terminal window and root-ray bridge inequalities, specializes the common error to 470, and invokes the mass-corridor consumer. These declarations compiled in run `45721351121`; the workflow rejects `sorryAx` across the transitive chain. The `native_decide` trust qualification above remains important.

The compiled chain now carries out these steps. Remaining work is to independently audit the coverage of the terminal-to-budget hypotheses against every source n=10 terminal parent, replace native-evaluated checkpoints with kernel-reduced proofs if feasible, and extend the argument beyond n=10.

If the checkpoint list and source bridge inequalities are confirmed, this proves that all four n=10 cancellation sectors are absent from the genuine blank-root orbit. It would resolve the entire n=10 terminal-budget layer, but it would not by itself resolve n>=11 or prove #623 nonhalting.

Keep this in `im-results/`; no claim belongs in `results/` until the source proof is complete.


## Fifth branch: even gap-two predecessor

The four ray wrappers do not cover the special even state (D(d+2,d)). Agent 48 identified a separate mass corridor:
`39362 <= (d+2)+d <= 118092` for `19680 <= d <= 59045`.

The source-transcribed checkpoints are run32 D(29194,9235), mass38429, and run37 D(41468,86104), mass127572. A root visit must be at steps 33–36; none of those four exact states has first coordinate equal to second+2. The Lean module includes `root_run_32` and `n10_even_gap_two_root_excluded`; this fifth-branch consumer compiled in run `45721351121`.


## Source-bridge composition still required

The conditional hypotheses are not orphaned: the source ingredients appear in `im-results/agent49-parity623/TerminalRatio4Source.lean` (four sector-specific terminal ratio-four windows) and `im-results/agent49-parity623/DrainLinearTerminalSource.lean` (four sector-specific signed root-ray gap bounds). The remaining task is to compose the matching pair per sector into each n=10 consumer: derive `hterm` and `B≤145` from the terminal-ratio theorem; derive `hbridgeLo/hbridgeHi`, `e≤306`, and the appropriate `cR/cL≤9` from the drain-linear gap theorem; then apply the matching `n10_*_bridge_excluded`. Variable alignment between predecessor, terminal, and blank-root states is the main proof obligation. This composition has not yet been compiled as a single theorem.
