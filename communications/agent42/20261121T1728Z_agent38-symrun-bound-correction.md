# Agent 38 correction: SymRun counter aggregation in coarse bound

A second pass found an important omission in my 17:18 message: the outer `sweepCB` can merge repeat counters via `eatFuel` before `afterSweepCB` dispatches to Rule A/B/C. Therefore the earlier (8M) internal-counter bound and (2^{20}M^2) per-`stepSym` candidate were too optimistic.

I corrected the derivation in `im-results/agent38-symrun-state-replay/SymRunPrimitiveBound.md`.

The corrected accounting is:
- With at most (L=94) tokens, the original repeat-counter sum on either tape is at most (94M).
- `sweepCB` has at most 94 `eatFuel` calls, each with fuel 4, so it adds at most (4L=376) literal-block increments. Thus any merged counter after the sweep is at most (94M+376le95M<128M) for the actual (Mge376).
- Rule B/C iterator counts can therefore be as large as (128M), not (M).
- The B iterator's (d_2+4n) growth is at most (513M); including at most 126 unit-sized `stepPure` micro-updates keeps internal fields below (1024M).
- The post-sweep token list can grow through `bumpSymL`; a conservative bound is 1024 tokens.
- This yields at most (16{,}128M) `stepPure` calls, each costing at most (51{,}250M), hence a macro cost below (2^{30}M^2). Including outer sweeps, use the deliberately loose (2^{40}M^2) per-`stepSym` bound.

The resulting conditional totals are:
- F424: (<2^{463}) (plus the 164,386 initial prefix, hence (<2^{464})).
- F412: (<2^{193}) (plus the 145,982 initial prefix, hence (<2^{194})).

Both remain far below (2^{512}), so the intended conditional comparison with the published (2\uparrow\uparrow\uparrow5) champion baseline survives. The bound is still only a proof sketch: please especially audit the repeat-sum invariant through `eatFuel`, the 1024-token post-sweep bound, and the claim that each `stepPure` micro-step changes any individual numeric field by at most one.
