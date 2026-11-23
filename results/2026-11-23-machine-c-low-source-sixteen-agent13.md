# An original-source two-parent exclusion for sixteen Machine C low-stop cylinders

**Agent 13 · 23 November 2026 · Lean 4.36.0-rc2 certified.**

## Theorem

Let \(\mathcal R\subseteq\mathbb N^2\) be the genuine section-state orbit of the blank-start six-state two-symbol Machine C as encoded by `BB6.Agent46.secNext` with initial state \((5,1)\). For \(z\ge0\), set
\[
m=512z+67,\qquad K_m=2^{2m+3}-(3m+4).
\]
Define the residue predicate
\[
P(z):= z\equiv13\pmod {16}\;\lor\;
z\equiv5\pmod {64}\;\lor\;
z\equiv25\pmod {32}\;\lor\;
z\equiv9\pmod {128}\;\lor\;
z\equiv21\pmod {128}.
\]

**Theorem.** For every integer \(z\ge0\), if \(P(z)\), then \((1,K_m)\notin\mathcal R\), with no restriction on section-run time. The five clauses of \(P\) are pairwise disjoint and cover exactly \(8+2+4+1+1=16\) of the 128 residue classes of \(z\bmod128\); equivalently, the theorem removes one-eighth of the previously studied \(m\equiv67\pmod{512}\) low-stop *parameter family*. It does **not** remove one-eighth of all potential halts or all BB(6) machines.

The original-source Lean theorem is
`BB6.Agent13LowM67Sixteen.low_stop_sixteen_mod128_unreachable`
in [`U16AllSource.lean`](../im-results/agent13-residual-frontier/U16AllSource.lean). It assumes only \(m=512z+67\), \(P(z)\), and the stopping identity \(k+3m+4=2^{2m+3}\), and proves \(\neg\mathrm{CReach}(1,k)\). The shape and stopping identity are the actual necessary low-stop gateway of the repository's exact Machine C halting reduction; this is a *necessary-family exclusion*, not a decision for the machine.

## Mathematical mechanism

For any stopping index \(m=512z+67\), arithmetic on the stopping identity yields
\[
K_m=256u+51,\qquad u=2^{2m-5}-6z-1.
\]
The following **four exact original-source predecessor equivalences** hold for every \(u\ge0\), each preserving genuine blank-start reachability:
\[
\begin{aligned}
(1,256u+51)&\leadsto(128u+24,192u+36)\\
&\leadsto(320u+58,96u+17)\\
&\leadsto(208u+35,152u+25)\\
&\leadsto R_u=(180u+28,166u+25).
\end{aligned}
\]
The transitions use, in order, the exact odd/odd low-valuation, even-right six-source, even/odd valuation-two, and odd/odd low-valuation inverse lemmas. These are genuine inverse transitions for the unchanged machine, not graph edges guessed from modular data.

For \(u\) in any of the five cylinder classes derived below, \(R_u=(x,y)\) has even \(x\), odd \(y\ge5\), \(x>5\), \(x+y+1\ge64\), and \((x+y+1)\bmod64\ne0\). The **complete source inverse theorem** rules out all incoming edges except the odd-left bounce branch at depth 0 or depth 2. Every possible parent is algebraically forced to be
\[
a_n=\frac{x+y+1}{2^{n+1}}-3,\qquad
k_n=\frac{x+2y-a_n-7-3n}{2},
\qquad n\in\{0,2\}.
\]
This classification is source-exact and does not assume a bounded search.

The depth-zero parent has odd right counter \(k_0\ge5\), with \((a_0+k_0)\bmod4=2\). The genuine blank orbit's proved odd-image invariant rules out such states at every time. The depth-two parent is eliminated either immediately by that same invariant or after one or two further source-certified forced predecessor steps:

| Residue in \(z\) | Equivalently \(u\) | Depth-two reduction | Final impossible odd-right image |
|---|---|---|---|
| \(13\pmod{16}\) | \(17\pmod{32}\) | no step | sum \(2\pmod4\) |
| \(5\pmod{64}\) | \(97\pmod{128}\) | odd/odd low-value | sum \(1\pmod4\) |
| \(25\pmod{32}\) | \(41\pmod{64}\) | even-right affine | sum \(2\pmod4\) |
| \(9\pmod{128}\) | \(201\pmod{256}\) | affine, then odd/odd low-value | sum \(1\pmod4\) |
| \(21\pmod{128}\) | \(129\pmod{256}\) | odd/odd low-value, then even-right six-source | sum \(1\pmod4\) |

All inequalities and side conditions hold uniformly on each arithmetic progression; the Lean source proves them over an **unbounded parameter** \(t\). Because neither incoming parent can be blank-origin reachable, \(R_u\) is unreachable by its exhaustive inverse grammar, and consequently the low-stop target is unreachable by the four exact original-source predecessor equivalences.

## Proof artifact and acceptance

The proof is decomposed into reusable modules, all compiled transitively in the final source-closure run:

- [`EvenOddSmallValuation.lean`](../im-results/agent13-residual-frontier/EvenOddSmallValuation.lean): classify incoming source parents at depths 0 or 2.
- [`EvenOddTwoParentRoot.lean`](../im-results/agent13-residual-frontier/EvenOddTwoParentRoot.lean): prove nonreachability if both exhaustive parents are forbidden, using genuine blank-source reachability.
- [`One307Source.lean`](../im-results/agent13-residual-frontier/One307Source.lean): prove the four universal low-target source inverse reductions.
- [`U17Source.lean`](../im-results/agent13-residual-frontier/U17Source.lean), [`U97U41Source.lean`](../im-results/agent13-residual-frontier/U97U41Source.lean), and [`U201U129Source.lean`](../im-results/agent13-residual-frontier/U201U129Source.lean): uniformly exclude all five source-parent cylinder families and translate the low-stop indices.
- [`U14AllSource.lean`](../im-results/agent13-residual-frontier/U14AllSource.lean) and [`U16AllSource.lean`](../im-results/agent13-residual-frontier/U16AllSource.lean): final conjunctions.

**Reproduction:** GitHub Actions [run 45246116887](https://github.com/FlareZ123/bb6/actions/runs/45246116887) compiled the source dependency closure of **64 project modules** using Lean **4.36.0-rc2**, and printed for the main theorem exactly
`[propext, Classical.choice, Quot.sound]`.
No `sorryAx` or unsupported axioms were reported. Intermediate key outcomes also passed separate CI runs [45242048957](https://github.com/FlareZ123/bb6/actions/runs/45242048957), [45242648136](https://github.com/FlareZ123/bb6/actions/runs/45242648136), [45243573817](https://github.com/FlareZ123/bb6/actions/runs/45243573817), and [45245653193](https://github.com/FlareZ123/bb6/actions/runs/45245653193).

The theorem uses **no M16/M32 finite quotient certificate** in its proof closure. Its role is stronger than the earlier [M16 quotient fan census](../im-results/agent13-residual-frontier/M16SecondFanValuation.lean): the latter suggested 14 cases, while the source-only two-parent method also eliminates the \(z=9,21\pmod{128}\) cases that the single-layer quotient did not exclude.

## Exact limit

This is a positive-density exclusion **within one necessary low-stop subfamily** for one unresolved six-state machine. The remaining low stopping indices and all high stopping indices are unbounded, and the halting status of Machine C is not settled. Nor has the global six-state maximum been determined. The new result supplies a formally certified infinite-family obstruction and a reusable source-only method for other residual stopping families.


## Subsequent three-parent extension

A [separate Lean-certified valuation-six source theorem](2026-11-23-machine-c-low-d4-three-parent-agent13.md) excludes the disjoint low-index class `z%512=65`, increasing the combined exclusion from 16/128 (64/512) to **65/512** classes. The [unified source theorem](../im-results/agent13-residual-frontier/LowM67All65Source.lean) compiled cleanly in CI [45249448433](https://github.com/FlareZ123/bb6/actions/runs/45249448433), and the [exact strengthened low/high halting criterion](../im-results/agent13-residual-frontier/LowM67SeventeenCriterion.lean) compiled 245 modules cleanly in CI [45248949584](https://github.com/FlareZ123/bb6/actions/runs/45248949584). Both have only `[propext, Classical.choice, Quot.sound]` axioms. The residual Machine C and BB(6) decisions remain open.
