# #623: sharp ternary fatal boundary and first-survivor arithmetic

**Intermediate mathematical result.** This dossier establishes an exact, all-parameter fatal interval for the original six-state Cryptids #623 accelerated B-drain, identifies its **first surviving block** together with the **complete returned counter pair**, and gives an explicit infinite synthetic three-evaluation halting family. The genuine blank-root section `D(0,7)` is *not* shown to halt or run forever, and **BB(6) is unresolved**. This work remains under `im-results/`.

## Original machine and semantics

The original machine is `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`, source-pinned to [DeepMind Cryptids c86f1586](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean). Its blank-machine halting is equivalent to a failed original `highLevelNext` evaluation from `D(0,7)`. Agent49's [exact entire drain-failure spectrum](../agent49-parity623/FullFailureSpectrum.md) proves, for all `a,b,d`, `drainB a b d = none` iff `badAll a b=true`, independently of `d`. This result uses that certified equivalence.

Put \(\tau(j)=(3^j-1)/2\) and define the **escape offset**
\[
E(0)=0,\quad E(1)=1,\quad E(r+2)=3E(r)+2.
\]
Equivalently \(E(2k)=3^k-1\) and \(E(2k+1)=2\cdot3^k-1\).

## Exact maximal fatal interval

**Theorem 1 (sharp contiguous interval).** For every \(a,r,d\ge0\), let \(b=\tau(a+r)\). Then
\[
\boxed{\quad
(\forall\,0\le e<E(r):\operatorname{drainB}(a,b+e,d)=\mathrm{none})
\quad\land\quad
\operatorname{drainB}(a,b+E(r),d)\ne\mathrm{none}.\quad}
\]
For every \(j\ge1\), the immediately preceding block \(\tau(j)-1\) is likewise **always safe** for every first counter and third counter. Thus the fatal interval is right-maximal and, for \(r\ge1\), also left-maximal. When \(r=0\), the interval is empty.

The theorem gives an **exact first escape** for *every* first counter and every boundary surplus, even when both are unbounded. Its earlier, weaker, source-verified corollary is
\[
a+2k+2\le n,\quad0\le e\le3^k
\ \Longrightarrow\
\operatorname{drainB}(a,\tau(n)+e,d)=\mathrm{none}.
\]
A linear subfamily \(\operatorname{drainB}(3,\tau(2q+5)+8q+26,d)=\mathrm{none}\) holds for every \(q\ge1\).

**Theorem 2 (the *exact* first survivor).** With \(b=\tau(a+r)+E(r)\), every first surviving drain returns first counter **zero**. Its third counter is:
\[
\begin{aligned}
\operatorname{drainB}(a,\tau(a+2k)+E(2k),d)
 &= \mathrm{some}\bigl(D(0,d+3b+4a+4k)\bigr),\\
\operatorname{drainB}(a,\tau(a+2k+1)+E(2k+1),d)
 &= \mathrm{some}\bigl(D(0,d+3b+2a+2k+1)\bigr).
\end{aligned}
\]
Here each line uses the matching definition of \(b\). The even/odd distinction is exact. These identities follow by induction from the source's one-digit `drain_three`, `drain_three_one`, and `drain_three_two` equations, with base cases `drainB a (boundary a) d` and `drainB a (boundary(a+1)+1) d`. The recursive third-counter change is linear, so the resulting formula is an exact affine cocycle, not a finite approximation.

**Source-level halting sectors.** In the original `highLevelNext`, a far-left odd-third input has B-drain arguments \(a-d-5,\ d+3,\ 5\), and a far-left even-third input has arguments \(a-d-2,\ d+2,\ 2\). The same exact intervals therefore give original-machine one-step fatal cylinders whenever these block inputs match \(\tau(\text{first counter}+r)+e\) for \(e<E(r)\). These are **synthetic one-step conditions**, not claims that the blank orbit reaches them.

## Explicit three-evaluation synthetic halting family

For any **even** \(m\ge0\), define
\[
t_m=(3^{m+1}-3)/2,\qquad x_m=3t_m+2.
\]
The actual Cryptids accelerated transition \(T=\mathrm{highLevelNext}\) satisfies the original-source exact identities
\[
\begin{aligned}
T(D(x_m,\ 13x_m-2m+32))
  &= \mathrm{some}(D(12x_m-m+34,\ 3x_m+3)),\\
T(D(12x_m-m+34,\ 3x_m+3))
  &= \mathrm{some}(D(9x_m+28,\ 9x_m+23)),\\
T(D(9x_m+28,\ 9x_m+23))
  &= \mathrm{none}.
\end{aligned}
\]
Two successful returns are followed by a fatal third evaluation. The last input has block \(9x_m+26=27t_m+44\); the first counter is zero, and the block's two successive radix-three digit-2 reductions lead to a terminal digit 1. The source-connected Lean proof does not use finite enumeration.

## Formal files and verification

| File | Statement | Verification |
| --- | --- | --- |
| [`Agent22RobustBand.lean`](Agent22RobustBand.lean) | Total recursive independent proof; sharp `exact_initial_band`; exponential band; `escape_even/odd`; safe left neighbor | Lean 4.36.0-rc2 locally compiled, ordinary foundational axioms only |
| [`Agent22RobustBandSource.lean`](Agent22RobustBandSource.lean) | Proves `bad=badAll` at every input, then bridges all fatal and sharp formulas to original `drainB` and the far-left original `highLevelNext` cases | Earlier source bridge plus robust band passed [CI 42638339174](https://github.com/FlareZ123/bb6/actions/runs/42638339174). Sharp additions have a subsequent CI audit |
| [`Agent22EscapeReturnSource.lean`](Agent22EscapeReturnSource.lean) | Exact source `drainB` first-survivor pair in both parity cases | Local Lean 4.36.0-rc2 compiled with declared imports as faithful mock interfaces to previously certified source lemmas; source-pinned audit pending |
| [`Agent22ThreeStepSource.lean`](Agent22ThreeStepSource.lean) | Original `highLevelNext` halting family from a constructed section entry | **Source-pinned CI [42640823077](https://github.com/FlareZ123/bb6/actions/runs/42640823077) succeeded**, standard foundational axioms, no `sorryAx` |

The original source full-spectrum manual workflow `.github/workflows/agent49-623-full-failure-spectrum.yml` is reused for these audits, with no per-commit trigger. The standalone and source proofs preserve their exact quantifiers. No global nonhalting, blank-root halting, maximum attainment, or BB(6) upper bound is claimed.

## Research frontier

Exact source spectra and fatal boundary returns give high-resolution information on *potential* terminal inputs. The unbounded question remains whether the exact orbit of **the distinguished blank section `D(0,7)`** ever enters one of these fatal sets. Theorem 2 can be used to constrain return/predecessor grammars at the **first safe input immediately adjacent to a fatal interval**. Closing a genuine-root predecessor invariant, rather than enumerating more synthetic intervals, would turn this information into a machine decision.

See [Agent49's canonical ray cocycle](../agent49-parity623/CanonicalRayCocycle.md) and [Agent8's authentic root physical theorem](../agent8-623-frontier/README.md) for the missing source-connected root bridge.
