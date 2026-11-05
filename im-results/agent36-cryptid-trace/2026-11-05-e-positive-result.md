# Original-source E positive-double-zero rule (2026-11-05)

**Kernel checked against the original D Cryptid machine**, `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.

Let `I_n(y)` mean F scanning 0, blank left, with `1^n y` to its right. For every `k,q,r ≥ 0` and every finite right suffix `y`:

```text
I_(3k+4)(0 (10)^(q+1) 110 (10)^r 0 y)
  --[12k²+49k+64+4q+4r]-->
I_(8k+5)(0 1^(2q+4) 0 1^(2r+6) y)
```

The input must have at least one `10` pair before `110`. The previously established zero-pair theorem is in [EZeroPairs0.lean](EZeroPairs0.lean), whose output differs.

New source proof: [Core0](EPositiveCore0.lean), [Core1](EPositiveCore1.lean), [return](EPositiveDoubleZero.lean), [packet algebra](EPositivePacket.lean), [clean formula](EPositiveSimplified.lean). It composes the real original machine, using arbitrary-parameter scan/turn lemmas and exact primitive times. **[Original-source Lean CI 42039675056](https://github.com/FlareZ123/bb6/actions/runs/42039675056) succeeded**; final axiom audit `[propext, Quot.sound]` only, no `sorryAx`.

Independent original-rule sparse-tape simulation agreed for 600 parameter combinations (`k<4`, `q,r<5`, six different right suffixes), including full physical first F/0 return and step count. The Lean theorem establishes a universal exact endpoint, without separately certifying first-return minimality.

This is **intermediate** work: the family begins on specified synthetic tapes. No blank-origin reachability theorem, resolved holdout, improved BB(6) bound, or claim of external novelty follows. The earliest missing E return in a residue-forgetting suffix exploration was an implicit-blank instance of this newly certified family. The residue-forgetting exploration cannot establish actual blank reachability.
