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


## Root phase and reset-family theorems

`Phase6.lean` proves that every positive-time state reachable from the authentic seed belongs to
`(a mod2,d mod6) ∈ {(0,1),(0,2),(1,5)}`. `Phase12.lean` refines this to a small mod-12 invariant and yields the exact reachable middle-even predecessor shape.

`ResetHigh.lean` combines the root invariant with the arbitrary High theorem. A reachable middle-odd reset followed only by High steps can hit the terminal diagonal only at a run length `k≡4 (mod8)`, with terminal parameter `D+3=4*2^k`.

`ResetEven.lean` proves the complementary middle-even result: a reachable middle-even reset followed only by High steps can hit the terminal diagonal only for `k mod16∈{7,11,15}`, with `D+3=5*2^k`. Thus the generic `k≡3 (mod4)` family loses its complete `3 mod16` subfamily.

`Phase6Bridge.lean` transports the local reachability invariant into the repository's canonical `CounterReach 1 1` relation. GitHub Actions runs 46128503550 and 46128963897 both completed successfully against the repository dependency closure.

A paper corollary of the two terminal formulas is that all sufficiently long middle-reset-to-High terminal candidates share `D≡4093 (mod12288)`; only the small parameters `61`, `637`, and `10237` precede that stable tail. The current uniform affine-ray generator does not close `4093 mod12288` because its inverse cone reaches a threshold case whose Far predecessor exists only for positive ray parameter. Splitting that boundary is the next concrete exact target.
