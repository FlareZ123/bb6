# F321 diagonal coordinates and kernel-checked bulk runs

This directory develops a source-faithful coordinate system for the exact F321 two-counter return map and closes a formalization gap in the existing bulk accelerator.

Define

```text
x = a + d + 5
y = 2(d + 3).
```

For every authentic counter state, `y` is even. The absent/halting branch `a=d+1` becomes the literal diagonal `x=y`. The five live branches become:

```text
high:         y < x       -> (x+1, 2y)
equal:        y = x+1     -> (x+5, 8)
far:          x+2 <= y and 3x <= 2y+2
                         -> (x+6, 4y+12-6x)
middle-even:  x+2 <= y and 2y+2 < 3x and x odd
                         -> (..., 10), output x == 1 (mod 4)
middle-odd:   x+2 <= y and 2y+2 < 3x and x even
                         -> (..., 8),  output x == 0 (mod 4).
```

`DiagonalCoordinates.lean` proves these identities directly from the exact `CounterMove` relation in `im-results/agent31-f321-bulk/SourceCounter.lean`. In particular, it proves `terminal_iff_diagonal` and `move_coordinate_cases`.

`BulkRuns.lean` defines source-faithful relations for consecutive high and far branches. It proves arbitrary-length high acceleration

```text
x_n = x_0 + n
y_n = 2^n y_0,
```

so a terminal endpoint obeys `x_0+n = 2^n y_0`. More importantly, it kernel-proves the far-run formulas that were previously only paper-level in the F321 bulk dossier. For `n` consecutive far steps from `(a,d)` to `(A,D)`:

```text
A + 2 = (a + 2) 4^n,
D + (a + 2)(4^n - 1) = d + 6n.
```

The second equality is a subtraction-free natural-number form of
`D = d - (a+2)(4^n-1) + 6n`, avoiding any ambiguity from truncated subtraction. If the far run exits directly at the terminal gate `A=D+1`, Lean derives

```text
a + d + 5 + 6n = 2(a+2)4^n.
```

Local Lean 4.36.0-rc2 compilation against the exact current `SourceCounter.lean` succeeds. Printed axiom profiles are standard only: high-run theorems use `propext, Classical.choice, Quot.sound`; far-run formula/terminal theorems use `propext, Quot.sound`; there is no `sorryAx` or `native_decide`.

## Status and use

This is an exact theorem about the published F321 source counter map, not an original-tape nonhalting proof, a Raw132 parent Cover, or a BB(6) upper bound. Its value is that arbitrary high/far epochs can now be compressed inside Lean without trusting the JavaScript bulk runner. The next high-value step is to build the maximal-exit selector and reset-to-reset invariant on top of these formulas, then connect that invariant through the already staged original-machine/high-level bridge.
