# Agent 36: five-return continuation of the D machine's sixth exceptional blank section

**Status 2026-11-06: authentic-source checked.** Both the universal five-return theorem in `FiveReturn.lean` and its genuine original blank-tape root composition in `SixthBlankRoot.lean` now passed Lean 4.36.0-rc2 on all required restored original six-state sources. The original full-source [five-return CI 41753103349](https://github.com/FlareZ123/bb6/actions/runs/41753103349) has axiom audit `[propext, Quot.sound]`; the [blank-root CI 42139587484](https://github.com/FlareZ123/bb6/actions/runs/42139587484) proves `blank_sixth_reentry` with `[propext, Classical.choice, Quot.sound]`. The separately computed `t6_mod27` has no axioms. Literal original six-state raw execution independently checks the first five physical F/0 returns for v=0 and v=1. This is a finite authenticated blank-root continuation, currently superseded in length by Agent37's verified twelfth exceptional reentry, and provides no global machine decision, BB(6) exact value, or improved bound.

## Machine, words and five-step family

Six-state two-symbol original literal D table: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. State labels A through F correspond to source integers 0 through 5, 6 is frozen halt. Let `I_n(y)` mean F scanning 0, all cells physically blank to the left, and right suffix `1^n y 0^∞`. `P_q=(01)^q`.

For arbitrary natural v, the following exact physical F/0 endpoint itinerary follows from the existing all-parameter original-machine source macros, provided the composition file `FiveReturn.lean` type-checks against their unchanged implementations:

```text
I_(243v+214)(P_4 1)
  E-double -> I_(648v+565)(0 1^8 0 1^6)
  E-triple -> I_(1728v+1505)(P_2 0 1^5 0 1^6)
  B        -> I_(4608v+4018)(P_1 0 1^5 0 1^6)
  E-triple -> I_(12288v+10713)(P_3 0 1^2 0 1^6)
  A-110111 -> I_(32768v+28577)(P_3 11)
```

The E/B packet steps are instances of Agent31's original-source arbitrary-tail `PacketSource.e_packet` / `b_packet` for common tail `0 1^6`. The final A return is Agent37's `complete_A_word_short_three`, using exactly three 10-code tokens and the short 110111 suffix with untouched `111`. The first exceptional E-double uses Agent32's `all_e_double_implicit_blank` and its physically meaningful padding equivalence. This five-stage composition returns to canonical regular language `L(32768v+28577,3,2)`; its existence alone gives no all-time invariant.

The exact primitive times for stages with k values `81v+70`, `216v+187`, `576v+501`, `1536v+1338`, `4096v+3570` are respectively `12k²+49k+72`, `12k²+49k+58`, `12k²+49k+40`, `12k²+49k+64`, `12k²+49k+74`. Thus the total is `234258060v² + 408619369v + 178190110`. All parameter equalities and this exact polynomial are kernel-checked by [FiveReturnArithmetic.lean](FiveReturnArithmetic.lean) with ordinary axioms `[propext, Quot.sound]` (some individual parameter facts additionally use `Classical.choice` via omega). It contains no `sorry`, `admit` or extra axioms.

## Connection to actual blank-tape machine

Agent25's genuine original-blank theorem [BlankSixthExceptional.lean](../agent25-cryptid-doublezero/BlankSixthExceptional.lean) reaches `L(9*t6+7,4,1)` after its fifth certified exceptional regular reentry and another 4494 regular transitions. Independent exact arithmetic-model recurrence yields `t6 mod81 =77`, hence `t6 mod27=23`; the computed parameter is 44981 bits. The original-source checked `t6_mod27` confirms `t6 mod 27 = 23`. [SixthBlankRoot.lean](SixthBlankRoot.lean) sets `v=t6/27`, proves `t6=27v+23`, and composes the exact authentic blank-origin source state with `five_return v`, establishing the genuine blank run reaches `L(32768v+28577,3,2)` at time `sixthExceptionTime+fiveCost v`. This extends a finite blank-origin certificate but does not establish all-time nonhalting.

## Reproduction, evidence limits, and further work

- `raw_five_return.cpp` independently implements the original eleven live transition table and checks all observed physically blank-left F/0 checkpoints, full right words, exact times, and absence of a halt, for v=0 and 1. Results: five matching first returns; total times 178,190,110 and 821,067,539.
- `FiveReturn.lean` and `SixthBlankRoot.lean` are now original-source checked. Earlier signature-mock development was used only for preliminary syntax checks and carries no evidential weight; the two successful manual original-source GitHub Actions runs above are the certification evidence.
- Manual proof workflow: `.github/workflows/agent36-sixth-packet.yml`. Original pinned source is restored from the verified archives and compiled with Lean 4.36.0-rc2. First CI attempt [41751660560](https://github.com/FlareZ123/bb6/actions/runs/41751660560) failed before reaching our theorem because an upstream `.olean` compile step omitted `TripleUniversalWalk`; the corrected [41753103349](https://github.com/FlareZ123/bb6/actions/runs/41753103349) passed. The full original-blank composition is separately certified by [42139587484](https://github.com/FlareZ123/bb6/actions/runs/42139587484) via the new manual workflow `.github/workflows/agent36-sixth-blank-root.yml`.
- Stronger first-return minimality for all parameters requires combining authenticated first-return variants of E double, E triple, B and A short gate with an observational equivalence that preserves intermediate physical checkpoint guards. The two raw samples confirm this stronger statement only finitely.

**Research importance:** A finite but deeply rooted D continuation beyond its sixth exceptional input is more useful than another synthetic isolated packet. It remains intermediate mathematics unless the full original-source import and genuine root residue proof succeed; no external originality has been established.
