# Agent 36: five-return continuation of the D machine's sixth exceptional blank section

**Status 2026-11-04:** interim result. All-parameter arithmetic is checked by Lean 4.36.0-rc2; literal original six-state raw execution independently checks the first five physical F/0 returns for v=0 and v=1. Full original-source theorem in `FiveReturn.lean`, and its genuine blank-start composition in `SixthBlankRoot.lean`, await successful CI. Do not describe either source candidate as kernel-certified until the workflow succeeds. The exact value of BB(6) and the D machine's all-time behavior remain unknown.

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

Agent25's genuine original-blank theorem [BlankSixthExceptional.lean](../agent25-cryptid-doublezero/BlankSixthExceptional.lean) reaches `L(9*t6+7,4,1)` after its fifth certified exceptional regular reentry and another 4494 regular transitions. Independent exact arithmetic-model recurrence yields `t6 mod81 =77`, hence `t6 mod27=23`; the computed parameter is 44981 bits. If the corresponding `t6_mod27` `by decide` check and actual original-source composition compile in [SixthBlankRoot.lean](SixthBlankRoot.lean), take `v=(t6-23)/27` to prove that the genuine blank run reaches `L(32768v+28577,3,2)` at the explicitly assembled original primitive clock. This extends a finite blank-origin certificate but does not prove nonhalting.

## Reproduction, evidence limits, and further work

- `raw_five_return.cpp` independently implements the original eleven live transition table and checks all observed physically blank-left F/0 checkpoints, full right words, exact times, and absence of a halt, for v=0 and 1. Results: five matching first returns; total times 178,190,110 and 821,067,539.
- `FiveReturn.lean` is a candidate direct composition against original source lemmas. A local *signature-mock* compilation was used only to catch syntax and list-congruence mistakes. Mock axioms give zero evidence of original-source correctness. Only a successful unchanged-source workflow can authorize this stronger claim.
- Manual proof workflow: `.github/workflows/agent36-sixth-packet.yml`. Original pinned source is restored from the verified archives and compiled with Lean 4.36.0-rc2. First CI attempt [41751660560](https://github.com/FlareZ123/bb6/actions/runs/41751660560) failed before reaching our theorem because an upstream `.olean` compile step omitted `TripleUniversalWalk`; workflow has been corrected and rerun.
- Stronger first-return minimality for all parameters requires combining authenticated first-return variants of E double, E triple, B and A short gate with an observational equivalence that preserves intermediate physical checkpoint guards. The two raw samples confirm this stronger statement only finitely.

**Research importance:** A finite but deeply rooted D continuation beyond its sixth exceptional input is more useful than another synthetic isolated packet. It remains intermediate mathematics unless the full original-source import and genuine root residue proof succeed; no external originality has been established.
