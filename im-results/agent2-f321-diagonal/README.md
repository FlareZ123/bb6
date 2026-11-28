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


## Current root-specific frontier (Agent 2, 2026-11-28)

The earlier `4093 mod 12288` boundary split is now partly resolved and, more
importantly, its genuine obstruction is structurally identified.

Kernel-accepted results now live under `results/`:

- `2026-11-28-f321-twelve-refined-4093-source-rays-agent2.md` proves twelve
  disjoint source-unreachable refinements modulo 786432, exactly 3/16 of the
  4093 parent ray (CI 46139830074).
- `2026-11-28-f321-minus-three-reset-tail-sieve-obstruction-agent2.md`
  identifies the authentic M1/M2 reset-to-High spines, proves both converge
  2-adically to -3, and proves that every fixed-depth `NoResidueWord`
  certificate is eventually defeated by the all-F inverse word on those
  authentic tails (CI 46139289738 and 46139762995).

The source-level response is now in `AnchorEpoch.lean`.  Equal and both Middle
branches are treated uniformly as **small-second anchors** (output second counter
1 or 2).  Every positive-time root run decomposes canonically into completed
anchor epochs separated by pure High/Far runs, followed by one final High/Far
suffix.  Consequently any hypothetical halt has a genuine root-reachable last
anchor and an exact terminal-seeded High/Far inverse word reaching that anchor,
with no large-second or bounded-depth cutoff.

The current committed source derives the following stronger pending-kernel
normal form:

- the final High/Far suffix is nonempty and its first **two** moves are High;
- only High can grow the second counter, so `D+3 <= 5*2^h` for some
  `h <= suffix length`;
- for inverse-word counts `H,F`,
  `shift=H+2F`, `sumDecrease=H+6F`, and
  `sumDecrease+4*length=5*shift`;
- the authentic last anchor obeys
  `R+c+5*shift = 2D+1+4*length`;
- `c=1` forces even High count, while `c=2` forces odd High count; together
  with the forced HH prefix this gives at least two Highs for c=1 and at least
  three for c=2.

These AnchorEpoch statements are intentionally retained in `im-results/`
until a source-closure runner slot is available; they are not yet promoted as
academic results.  Queue pressure was severe (Critic broadcast at 11:53 UTC),
so stale/secondary Agent-2 audits were cancelled rather than competing with
the global Canonical38/Raw112/Raw42 acceptance path.

Finally, `DiagonalCoordinates.lean` now also contains the direct rank theorem
that every live `CounterMove` increases `X=a+d+5` by at least one, hence
any terminal gate `(D+1,D)` reached in `n` source-counter moves satisfies
`n+1 <= 2D`.  This is committed as intermediate source structure pending the
next kernel audit.
