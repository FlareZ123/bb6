# Agent 12: direct EL/DR sweep factorization of the root countdown

**22 November 2026.** Added the phase decomposition to
`im-results/agent12-cryptid-root-invariant/RootCountdownGrowth.md`.

For the authentic no-swap #85 stack coordinates, let
`D_n(c)=CR([0],0^(4n+5)++[c])`, where `0=(0,0)`, `1=(1,0)` and `c≥3`.
The countdown can be proved without the larger shared-corridor family by factoring it into:

1. A fixed eight-successor prefix, raw costs `2,2,1,4,4,1,1,6` (21 raw steps), reaching
   `EL(L=[0,1], R=0^(4n+6)++[c])).
2. An EL-right-zero sweep of `4n+6` successors, each `execute 2`, reaching
   `EL(L=0^(4n+7)++[1],R=[c])).
3. EL-positive then DL-positive, two successors costing `1+4`, reaching
   `DR(L=0^(4n+7)++[1],R=[1,c-3])).
4. A DR-left-zero/right-one sweep of `4n+7` successors, each `execute 4`, reaching
   `DR(L=[1],R=[1]++0^(4n+7)++[c-3])).
5. One DR-positive/positive successor, `execute 3`, reaching
   `CR(L=[0],R=0^(4n+9)++[c-3])=D_(n+1)(c-3)`.

Hence the outer count is
`8+(4n+6)+2+(4n+7)+1=8n+24`,
and the raw cost is
`21+2(4n+6)+5+4(4n+7)+3=24n+69`.

The only parameterized proof components are two simple inductive sweeps, with one-step source lemmas:
- `EL(L,0::R) -> EL(0::L,R)` in 2 raw steps, copied from #85 `mode_EL_n_n_closed` lines 969–973.
- `DR(0::L,1::R) -> DR(L,1::0::R)` in 4 raw steps, copied from `mode_DR_n_n_closed` lines 1049–1056.

The fixed prefix can be composed from the corresponding CR/EL/DL/DR source branches. No token-normalizer branch is used in this countdown factorization. I source-transcribed and executed the phase endpoints for n=0,1,2; all endpoints and counts match. This is a proof plan and bounded computation, not yet a compiled quantified theorem. The existing corridor derivation and all caveats remain intact.
