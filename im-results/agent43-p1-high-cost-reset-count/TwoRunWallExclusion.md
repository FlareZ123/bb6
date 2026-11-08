# P1: exact affine invariant for unbounded depth-two inverse suffixes

**Scope and status (8 November 2026).** The following is a locally kernel-checked Lean 4.36.0-rc2 theorem about the **exact arithmetic transition equations** of P1's source inverse map. The transition equations agree with the original-source formulas stated and certified in [Agent50's energy dossier](../agent50-p1-subwall/README.md), especially its depth-two cocycle. The new exclusion is currently proven for a separately defined `TwoRun` relation; a complete source-level `CountCone`/original-`inverseAt` wrapper has **not yet** been built. This is an intermediate inverse-word obstruction, not a nonhalting theorem, not a right-five complete exclusion, and not a BB(6) result.

## Statement

Let (P=2^n), (n\ge 14), and define shifted wall (W=b+4m+4n+20) and auxiliary cost (B=m+n+6). For a genuine original-source depth-two inverse edge, Agent50's source identities give

```text
8 W_next = W + 84 P + 16 B,
B_next = B+3.
```

The affine defect

```text
I(P,W,B) = 49 W - 588 P - 112 B + 384
```

therefore satisfies the **exact identity** `I_next=I_before/8`. For every natural length `r`, the separately formalized `TwoRun` relation proves

```text
I(P,W_start,B_start) = 8^r I(P,W_end,B_end),
B_end = B_start + 3r.
```

The source root is `(b,d,m)=(14P-2n-16,3,0)`. Its first inverse edge, when depth zero or one, respectively has the exact arithmetic consequences:

```text
t=0: W_start = 7P+3n+10,  B_start=n+7
t=1: 2 W_start = 21P+5n+22, B_start=n+8.
```

**Two source-shaped exclusions**: No `TwoRun` of any length `r\ge0` from either of the above starting coordinates reaches `W_end=12P`, for any `n\ge14`. These exclude the infinite inverse-depth patterns `0,2,2,...,2` and `1,2,2,...,2` as *necessary arithmetic wall precursors*. They do not prohibit general inverse words containing other depths, and do not claim any source-level reachability assertion beyond the explicitly cited identities.

## Proof mechanism

Introduce `I` as above. Substituting the initial and final wall coordinates into `I_start = 8^r I_end` reduces the t=0 and t=1 cases to the respective natural-number equations

```text
245*2^n = (112*n+336*r+400)*8^r + (35*n+90)
147*2^n = (224*n+672*r+1024)*8^r + (21*n+54).
```

Both have no solution for `n>=14`. The common dyadic remainder lemma states: if `K*2^n = A*8^r+B` and `0<B<2^n`, then `3r<=n` and `8^r<=B`. The first assertion follows from considering which of `2^n` and `8^r` divides the other. Since `8^r|B` and `B>0`, the second follows immediately. Consequently `K*2^n <=(A+1)*B`, where `r<=n/3` makes the right side quadratic in `n`. Inductively certified exponential gaps give

```text
10125*(n+2)^2 < 245*2^n   for n>=14
13851*(n+2)^2 < 147*2^n   for n>=15.
```

The `n=14` t=1 case is handled by a bounded remainder argument (`r<=2`). This closes all natural `n,r` without sampling, an a priori run-length bound, or a fixed inverse cost.

## Source and verification boundary

- [DyadicGap.lean](DyadicGap.lean): the general modular remainder theorem and both all-natural number-theoretic exclusions.
- [TwoRunModel.lean](TwoRunModel.lean): exact affine recurrence and its `8^r` invariant for **all** finite runs.
- [TwoRunBridge.lean](TwoRunBridge.lean): two public wall-exclusion theorems combining the recurrence with the initial/source-shaped equations.
- Local Lean 4.36.0-rc2 compile commands: `lean -o DyadicGap.olean DyadicGap.lean`, then `lean -o TwoRunModel.olean TwoRunModel.lean`, then `lean TwoRunBridge.lean` with `LEAN_PATH` containing the directory of the first two `.olean` files. The public theorem axiom audits printed `[propext, Quot.sound]` only; neither theorem used `sorry`.
- A later proof **must** build the start-step bridge and transfer `TwoRun` by induction over the **unchanged original** `inverseAt`. All use of original source here is in the recurrence identities from [Agent50's source proof](../agent50-p1-subwall/RightFiveEnergyStep.lean), not a newly compiled full-source theorem.
- Original mathematical novelty remains unreviewed. Agent50 has independently proved a far more general near-wall reset-density *necessary bound*, [source CI 42520350507](https://github.com/FlareZ123/bb6/actions/runs/42520350507); this new exact-pattern obstruction is complementary and significantly narrower.

## Next high-value question

The direct-root shallow transition is the smallest case. Extend the defect method to **arbitrarily many depth-two steps before the single shallow edge**, i.e. patterns `2^s · (0|1) · 2^r`, where both `s` and `r` are unbounded. Initial calculations reduce the problem to a two-variable dyadic remainder with `8^s | (98*2^n-14*n-92)`. If successful, first formalize this as a pure arithmetic theorem, then close the authentic original-source bridge. General words with multiple shallow transitions or depth>=3 remain open.
